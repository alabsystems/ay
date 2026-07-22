// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::bool_normalization::normalize_bool_to_int;
use super::*;
use crate::pdr::solver::core;
use crate::pdr::solver::{
    compute_interpolant, compute_interpolant_from_lia_farkas,
    extract_interpolant_from_precomputed_farkas, interpolating_sat_constraints,
    InterpolatingSatResult, InterpolationDiagnostics, InterpolationFailure,
};
use crate::proof_interpolation::InterpolantKind;
use crate::smt::types::FarkasConflict;

pub(in crate::pdr::solver) struct InterpolationResult {
    pub(in crate::pdr::solver) formula: ChcExpr,
    pub(in crate::pdr::solver) kind: Option<InterpolantKind>,
    pub(in crate::pdr::solver) has_bool_normalization: bool,
    pub(in crate::pdr::solver) all_bool_vars: FxHashSet<String>,
}

impl PdrSolver {
    pub(in crate::pdr::solver) fn run_interpolation_cascade(
        &mut self,
        pob: &ProofObligation,
        transition_constraints: Vec<ChcExpr>,
        clause_interpolation_data: Vec<ClauseInterpolationData>,
    ) -> InterpolationResult {
        if self.config.verbose {
            safe_eprintln!(
                "PDR: Step 3 - transition_constraints.len()={}, use_interpolation={}",
                transition_constraints.len(),
                self.config.use_interpolation
            );
        }

        let mut has_bool_normalization = false;
        let mut all_bool_vars: FxHashSet<String> = FxHashSet::default();
        let mut interpolant_kind = None;
        let generalized = if !transition_constraints.is_empty() {
            let pre_prop_a_vars: FxHashSet<String> = transition_constraints
                .iter()
                .flat_map(ChcExpr::vars)
                .map(|v| v.name)
                .collect();

            let pre_prop_has_ite = transition_constraints.iter().any(has_ite_term);
            let pre_prop_transition = if pre_prop_has_ite {
                Some(transition_constraints.clone())
            } else {
                None
            };

            let transition_constraints: Vec<ChcExpr> = transition_constraints
                .into_iter()
                .map(|c| {
                    c.propagate_constants()
                        .simplify_linear_equalities()
                        .simplify_constants()
                })
                .flat_map(|c| c.collect_conjuncts())
                .collect();

            let bad_state_constraints = pob.state.collect_conjuncts();

            let canonical_names: FxHashSet<String> = self
                .canonical_vars(pob.predicate)
                .map(|vars| vars.iter().map(|v| v.name.clone()).collect())
                .unwrap_or_default();
            let raw_a_vars: FxHashSet<String> = pre_prop_a_vars.clone();
            let raw_b_vars: FxHashSet<String> = bad_state_constraints
                .iter()
                .flat_map(ChcExpr::vars)
                .map(|v| v.name)
                .collect();
            let raw_shared_vars: FxHashSet<String> = raw_a_vars
                .intersection(&raw_b_vars)
                .filter(|v| canonical_names.contains(*v))
                .cloned()
                .collect();

            let (norm_a, a_bool_vars) = normalize_bool_to_int(&transition_constraints);
            let (norm_b, b_bool_vars) = normalize_bool_to_int(&bad_state_constraints);
            all_bool_vars = a_bool_vars.union(&b_bool_vars).cloned().collect();
            has_bool_normalization = !all_bool_vars.is_empty();

            let interp_a = if has_bool_normalization {
                &norm_a
            } else {
                &transition_constraints
            };
            let interp_b = if has_bool_normalization {
                &norm_b
            } else {
                &bad_state_constraints
            };

            let post_prop_a_vars: FxHashSet<String> = interp_a
                .iter()
                .flat_map(ChcExpr::vars)
                .map(|v| v.name)
                .collect();
            let a_vars: FxHashSet<String> =
                pre_prop_a_vars.union(&post_prop_a_vars).cloned().collect();
            let b_vars: FxHashSet<String> = interp_b
                .iter()
                .flat_map(ChcExpr::vars)
                .map(|v| v.name)
                .collect();
            let shared_vars: FxHashSet<String> = a_vars
                .intersection(&b_vars)
                .filter(|v| canonical_names.contains(*v))
                .cloned()
                .collect();

            let pred_has_bv = self.canonical_vars(pob.predicate).map_or(false, |vars| {
                vars.iter().any(|v| matches!(v.sort, ChcSort::BitVec(_)))
            });
            if pred_has_bv && !self.problem_is_pure_lia {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: #5877 BV predicate — trying raw IUC B-core before BV inductive fallback"
                    );
                }
                if let Some(candidate) = self.try_iuc_farkas_fallback_candidate(
                    &transition_constraints,
                    &bad_state_constraints,
                    &raw_shared_vars,
                ) {
                    let kind = candidate.kind;
                    interpolant_kind = Some(kind);
                    let has_farkas_conflicts = candidate.has_farkas_conflicts;
                    let interpolant = candidate.expr;
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: #5877 BV direct-IUC candidate succeeded: {} (kind={:?}, has_farkas_conflicts={})",
                            interpolant,
                            kind,
                            has_farkas_conflicts,
                        );
                    }
                    ChcExpr::not(interpolant)
                } else {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: #5877 BV direct-IUC candidate unavailable; falling back to BV inductive generalization"
                        );
                    }
                    self.generalize_bv_inductive(&pob.state, pob.predicate, pob.level)
                }
            } else {
                let mut diag = InterpolationDiagnostics::new();

                if shared_vars.is_empty() {
                    diag.golem_sat = Some(InterpolationFailure::SharedVarsEmpty {
                        a_vars: a_vars.len(),
                        b_vars: b_vars.len(),
                    });
                }

                self.telemetry.interpolation_stats.attempts += 1;
                self.telemetry
                    .interpolation_stats
                    .debug_assert_consistency();

                let skip_conjunctive = if interp_a.len() < 2 {
                    false
                } else {
                    let a_side = self.bound_int_vars(ChcExpr::and_all(interp_a.iter().cloned()));
                    if self.incremental_pdr_enabled() {
                        let check_timeout = self.smt.current_timeout();
                        let prop = core::ensure_prop_solver_split(
                            &mut self.prop_solvers,
                            &self.frames,
                            pob.predicate,
                        );
                        matches!(
                            prop.check_feasibility(pob.level, &a_side, check_timeout),
                            IncrementalCheckResult::Unsat
                        )
                    } else {
                        // #7984: Use persistent executor backend for integer arithmetic.
                        matches!(
                            self.check_sat_via_executor_backend(&a_side),
                            SmtResult::Unsat
                                | SmtResult::UnsatWithCore(_)
                                | SmtResult::UnsatWithFarkas(_)
                        )
                    }
                };
                if skip_conjunctive {
                    self.telemetry.interpolation_stats.golem_a_unsat_skips += 1;
                    self.telemetry
                        .interpolation_stats
                        .debug_assert_consistency();
                    if diag.golem_sat.is_none() {
                        diag.golem_sat = Some(InterpolationFailure::NotApplicable {
                            reason:
                                "conjunctive A-side UNSAT (cross-clause contradiction); skipped"
                                    .to_string(),
                        });
                    }
                }
                let interpolant_result = if skip_conjunctive {
                    InterpolatingSatResult::Unknown
                } else {
                    interpolating_sat_constraints(interp_a, interp_b, &shared_vars)
                };

                match interpolant_result {
                    // #6002: Reject trivial interpolants (true/false) from conjunctive method.
                    // Bool(false) → Not(false) = true blocking formula (blocks everything, unsound).
                    // Bool(true)  → Not(true) = false blocking formula (blocks nothing, useless).
                    InterpolatingSatResult::Unsat(interpolant)
                        if !matches!(interpolant, ChcExpr::Bool(false) | ChcExpr::Bool(true)) =>
                    {
                        self.telemetry.interpolation_stats.golem_sat_successes += 1;
                        self.telemetry
                            .interpolation_stats
                            .debug_assert_consistency();
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: Interpolation-based lemma learning succeeded: {}",
                                interpolant
                            );
                        }
                        ChcExpr::not(interpolant)
                    }
                    _ => {
                        if matches!(
                            &interpolant_result,
                            InterpolatingSatResult::Unsat(
                                ChcExpr::Bool(false) | ChcExpr::Bool(true)
                            )
                        ) && self.config.verbose
                        {
                            safe_eprintln!(
                                "PDR: Rejecting trivial interpolant from conjunctive method — falling through to per-clause"
                            );
                        }

                        if diag.golem_sat.is_none() {
                            diag.golem_sat = Some(InterpolationFailure::NotApplicable {
                                reason: "no Farkas/bound/transitivity interpolant found"
                                    .to_string(),
                            });
                        }

                        let clause_data: Vec<(Vec<ChcExpr>, ChcExpr)> = clause_interpolation_data
                            .iter()
                            .map(|d| {
                                (
                                    d.head_args.clone(),
                                    d.constraint
                                        .propagate_constants()
                                        .simplify_linear_equalities(),
                                )
                            })
                            .collect();

                        if let Some(candidate) = self.try_n1_per_clause_interpolation(
                            &clause_data,
                            &pob.state,
                            pob.predicate,
                        ) {
                            self.telemetry.interpolation_stats.n1_per_clause_successes += 1;
                            self.telemetry
                                .interpolation_stats
                                .debug_assert_consistency();
                            let kind = candidate.kind;
                            interpolant_kind = Some(kind);
                            let has_farkas_conflicts = candidate.has_farkas_conflicts;
                            let interpolant = candidate.expr;
                            let weakened =
                                self.try_weaken_interpolant_equalities(&interpolant, &pob.state);
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: N1 per-clause interpolation succeeded: {} (weakened: {}, kind={:?}, has_farkas_conflicts={})",
                                    interpolant,
                                    weakened,
                                    kind,
                                    has_farkas_conflicts,
                                );
                            }
                            ChcExpr::not(weakened)
                        } else {
                            diag.n1_per_clause = Some(InterpolationFailure::NotApplicable {
                                reason: "per-clause interpolation failed".to_string(),
                            });

                            let all_clause_farkas: Vec<FarkasConflict> = clause_interpolation_data
                                .iter()
                                .flat_map(|d| d.farkas_conflicts.iter().cloned())
                                .collect();
                            let precomputed_result = if all_clause_farkas.is_empty() {
                                None
                            } else {
                                if self.config.is_lia_farkas_profile() {
                                    self.telemetry.lia_farkas_templates.record_farkas_check();
                                }
                                extract_interpolant_from_precomputed_farkas(
                                    &mut self.smt,
                                    interp_a,
                                    interp_b,
                                    all_clause_farkas,
                                    &shared_vars,
                                )
                            };
                            if let Some(interpolant) = precomputed_result {
                                self.telemetry.interpolation_stats.lia_farkas_successes += 1;
                                self.telemetry
                                    .interpolation_stats
                                    .debug_assert_consistency();
                                let weakened = self
                                    .try_weaken_interpolant_equalities(&interpolant, &pob.state);
                                if self.config.verbose {
                                    safe_eprintln!(
                                        "PDR: Precomputed clause-local Farkas interpolation succeeded: {} (weakened: {})",
                                        interpolant, weakened
                                    );
                                }
                                ChcExpr::not(weakened)
                            } else {
                                if self.config.is_lia_farkas_profile() {
                                    self.telemetry.lia_farkas_templates.record_farkas_check();
                                }
                                if let Some(interpolant) = compute_interpolant_from_lia_farkas(
                                    &mut self.smt,
                                    interp_a,
                                    interp_b,
                                    &shared_vars,
                                ) {
                                    self.telemetry.interpolation_stats.lia_farkas_successes += 1;
                                    self.telemetry
                                        .interpolation_stats
                                        .debug_assert_consistency();
                                    let weakened = self.try_weaken_interpolant_equalities(
                                        &interpolant,
                                        &pob.state,
                                    );
                                    if self.config.verbose {
                                        safe_eprintln!(
                                            "PDR: Proof-based Farkas interpolation succeeded: {} (weakened: {})",
                                            interpolant, weakened
                                        );
                                    }
                                    ChcExpr::not(weakened)
                                } else {
                                    diag.lia_farkas = Some(InterpolationFailure::NotApplicable {
                                        reason: "proof-based Farkas failed".to_string(),
                                    });

                                    if self.config.is_lia_farkas_profile() {
                                        self.telemetry.lia_farkas_templates.record_farkas_check();
                                    }
                                    if let Some(interpolant) =
                                        compute_interpolant(interp_a, interp_b, &shared_vars)
                                    {
                                        self.telemetry
                                            .interpolation_stats
                                            .syntactic_farkas_successes += 1;
                                        self.telemetry
                                            .interpolation_stats
                                            .debug_assert_consistency();
                                        let weakened = self.try_weaken_interpolant_equalities(
                                            &interpolant,
                                            &pob.state,
                                        );
                                        if self.config.verbose {
                                            safe_eprintln!(
                                                "PDR: Syntactic Farkas interpolation succeeded: {} (weakened: {})",
                                                interpolant, weakened
                                            );
                                        }
                                        ChcExpr::not(weakened)
                                    } else {
                                        diag.syntactic_farkas =
                                            Some(InterpolationFailure::NotApplicable {
                                                reason: "syntactic Farkas failed".to_string(),
                                            });

                                        if self.config.is_lia_farkas_profile() {
                                            self.telemetry
                                                .lia_farkas_templates
                                                .record_farkas_check();
                                        }
                                        if let Some(candidate) = self
                                            .try_iuc_farkas_fallback_candidate(
                                                interp_a,
                                                interp_b,
                                                &shared_vars,
                                            )
                                        {
                                            self.telemetry
                                                .interpolation_stats
                                                .iuc_farkas_successes += 1;
                                            self.telemetry
                                                .interpolation_stats
                                                .debug_assert_consistency();
                                            let kind = candidate.kind;
                                            interpolant_kind = Some(kind);
                                            let has_farkas_conflicts =
                                                candidate.has_farkas_conflicts;
                                            let interpolant = candidate.expr;
                                            let weakened = self.try_weaken_interpolant_equalities(
                                                &interpolant,
                                                &pob.state,
                                            );
                                            if self.config.verbose {
                                                safe_eprintln!(
                                                    "PDR: IUC-Farkas fallback succeeded: {} (weakened: {}, kind={:?}, has_farkas_conflicts={})",
                                                    interpolant,
                                                    weakened,
                                                    kind,
                                                    has_farkas_conflicts,
                                                );
                                            }
                                            ChcExpr::not(weakened)
                                        } else {
                                            diag.iuc_farkas =
                                                Some(InterpolationFailure::NotApplicable {
                                                    reason: "IUC-Farkas fallback failed"
                                                        .to_string(),
                                                });

                                            let d11_result = if let Some(ref pre_prop) =
                                                pre_prop_transition
                                            {
                                                if self.config.is_lia_farkas_profile() {
                                                    self.telemetry
                                                        .lia_farkas_templates
                                                        .record_farkas_check();
                                                }
                                                let pre_prop_b = &bad_state_constraints;
                                                if self.config.verbose {
                                                    safe_eprintln!(
                                                            "PDR: D11 pre-prop fallback: {} A-constraints, {} B-constraints, {} shared_vars",
                                                            pre_prop.len(), pre_prop_b.len(), shared_vars.len(),
                                                        );
                                                }
                                                crate::interpolation::core_ite_farkas::compute_ite_farkas_interpolant(
                                                        pre_prop,
                                                        pre_prop_b,
                                                        &shared_vars,
                                                    )
                                            } else {
                                                None
                                            };

                                            if let Some(interpolant) = d11_result {
                                                self.telemetry
                                                    .interpolation_stats
                                                    .lia_farkas_successes += 1;
                                                self.telemetry
                                                    .interpolation_stats
                                                    .debug_assert_consistency();
                                                let weakened = self
                                                    .try_weaken_interpolant_equalities(
                                                        &interpolant,
                                                        &pob.state,
                                                    );
                                                if self.config.verbose {
                                                    safe_eprintln!(
                                                        "PDR: D11 pre-propagation ITE-Farkas interpolation succeeded: {} (weakened: {})",
                                                        interpolant, weakened
                                                    );
                                                }
                                                ChcExpr::not(weakened)
                                            } else {
                                                self.telemetry.interpolation_stats.all_failed += 1;
                                                self.telemetry
                                                    .interpolation_stats
                                                    .debug_assert_consistency();
                                                debug_assert!(
                                                    diag.all_failed(),
                                                    "Expected all interpolation methods to fail at this point"
                                                );
                                                if self.config.verbose {
                                                    safe_eprintln!(
                                                        "PDR: Interpolation failed ({}/5 methods: {}), falling back to heuristic generalization",
                                                        diag.failure_count(),
                                                        diag.summary()
                                                    );
                                                    safe_eprintln!(
                                                        "PDR: Failure details:\n{}",
                                                        diag.detailed_summary()
                                                    );
                                                }
                                                self.generalize_blocking_formula(
                                                    &pob.state,
                                                    pob.predicate,
                                                    pob.level,
                                                )
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        } else {
            self.generalize_blocking_formula(&pob.state, pob.predicate, pob.level)
        };

        InterpolationResult {
            formula: generalized,
            kind: interpolant_kind,
            has_bool_normalization,
            all_bool_vars,
        }
    }
}

fn has_ite_term(expr: &ChcExpr) -> bool {
    match expr {
        ChcExpr::Op(ChcOp::Ite, _) => true,
        ChcExpr::Op(_, args) => args.iter().any(|a| has_ite_term(a)),
        _ => false,
    }
}
