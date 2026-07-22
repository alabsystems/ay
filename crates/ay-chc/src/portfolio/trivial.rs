// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Trivial-solve shortcuts for the CHC portfolio.
//!
//! When preprocessing inlines away all predicates, the problem reduces to
//! checking whether query constraints are satisfiable. This module handles
//! that special case without invoking the full engine portfolio.

use super::{PortfolioResult, PortfolioSolver, ValidationResult};
use crate::expr::evaluate_expr;
use crate::pdr::{Counterexample, InvariantModel, PredicateInterpretation};
use crate::smt::{SmtContext, SmtResult, SmtValue};
use crate::transform::{
    ClauseInliner, DeadParamEliminator, LocalVarEliminator, TransformationPipeline,
};
use crate::{ChcExpr, ChcProblem, ChcVar};

impl PortfolioSolver {
    /// Try to solve trivially-inlined problems.
    ///
    /// After preprocessing (ClauseInliner), if all predicates are inlined away,
    /// the problem reduces to checking if query constraints are satisfiable.
    /// If all query constraints are unsatisfiable, the problem is Safe.
    /// If any query constraint is satisfiable, the problem is Unsafe.
    pub(super) fn try_solve_trivial(&self) -> Option<PortfolioResult> {
        // Check if any clause has predicates in its body
        let has_body_predicates = self
            .problem
            .clauses()
            .iter()
            .any(|c| !c.body.predicates.is_empty());

        if has_body_predicates {
            return None; // Not a trivial problem
        }

        // All clauses have empty body predicates. Run one more local-var pass
        // before checking queries: clause inlining can leave Array-valued local
        // equalities in predicate-free formulas, and eliminating them exposes
        // read-over-write simplifications that prove the query UNSAT.
        let cleaned_problem = LocalVarEliminator::new().eliminate(&self.problem);
        let query_problem: &ChcProblem = &cleaned_problem;
        let queries: Vec<_> = query_problem.queries().collect();
        if queries.is_empty() {
            // No queries means trivially safe
            if self.config.verbose {
                safe_eprintln!("Portfolio: Trivially safe (no query clauses)");
            }
            let model = self.trivial_safe_candidate_model();
            return self.accept_validated_trivial_safe(model, "no queries");
        }

        // Check if any query constraint is satisfiable
        let mut smt = self.problem.make_smt_context();
        for query in &queries {
            let constraint = query.body.constraint.clone().unwrap_or(ChcExpr::Bool(true));

            let query_check = if constraint.vars().is_empty() {
                match evaluate_expr(&constraint, &ay_core::kani_compat::DetHashMap::default()) {
                    Some(SmtValue::Bool(true)) => {
                        SmtResult::Sat(ay_core::kani_compat::DetHashMap::default())
                    }
                    Some(SmtValue::Bool(false)) => SmtResult::Unsat,
                    _ => SmtResult::Unknown,
                }
            } else {
                smt.reset();
                smt.check_sat(&constraint)
            };

            match query_check {
                SmtResult::Sat(_model) => {
                    // Query constraint is satisfiable in the (possibly abstracted) domain.
                    //
                    // If BV-to-Int abstraction was applied, this SAT result may be spurious:
                    // the integer model may not map to valid bitvector values. BV-to-Int is
                    // an over-approximation (SAFE in Int → SAFE in BV, but UNSAFE in Int
                    // does NOT imply UNSAFE in BV).
                    //
                    // To confirm: inline the original (un-abstracted) problem and check
                    // whether its query constraints are also satisfiable in the native
                    // BV domain. If so, the system is genuinely unsafe (#6781).
                    if self.bv_abstracted {
                        if self.config.verbose {
                            safe_eprintln!(
                                "Portfolio: Trivial query SAT after BV-to-Int abstraction — \
                                 confirming against original problem"
                            );
                        }
                        if let Some(result) = self.confirm_trivial_unsafe_on_original(&mut smt) {
                            return Some(result);
                        }
                        if self.config.verbose {
                            safe_eprintln!(
                                "Portfolio: Original-domain confirmation failed, \
                                 falling through to engines"
                            );
                        }
                        return None;
                    }

                    // MUST-FIX A (rank-6 review, wrong-Unsat path): this SAT
                    // result was established on the TRANSFORMED problem. If
                    // any non-identity preprocessing ran (clause inlining,
                    // graph collapse, ...), a transform bug that weakens
                    // clauses would surface here as an unconfirmed Unsafe with
                    // no original-clause replay. Confirm unsafety against the
                    // ORIGINAL clauses (same helper the BV-abstraction path
                    // uses); if confirmation cannot be established, fail
                    // closed and fall through to the engines.
                    if !self.transform_memory.is_identity_grade() {
                        if self.config.verbose {
                            safe_eprintln!(
                                "Portfolio: Trivial query SAT on transformed problem \
                                 (non-identity transform stack) — confirming against \
                                 original problem"
                            );
                        }
                        if let Some(result) = self.confirm_trivial_unsafe_on_original(&mut smt) {
                            return Some(result);
                        }
                        if self.config.verbose {
                            safe_eprintln!(
                                "Portfolio: Original-clause confirmation failed for \
                                 transformed trivial Unsafe; falling through to engines \
                                 (fail closed)"
                            );
                        }
                        return None;
                    }

                    // Identity transform stack — the "transformed" problem IS
                    // the original, so the SAT result is reliable. System is
                    // unsafe.
                    if self.config.verbose {
                        safe_eprintln!(
                            "Portfolio: Trivially unsafe (query constraint satisfiable)"
                        );
                    }
                    return Some(PortfolioResult::Unsafe(Counterexample {
                        steps: Vec::new(),
                        witness: None,
                        ground_derivation: None,
                    }));
                }
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                    // This query is unreachable, continue checking
                }
                SmtResult::Unknown => {
                    // Can't determine - fall through to engines
                    if self.config.verbose {
                        safe_eprintln!(
                            "Portfolio: Trivial query check returned Unknown; falling through to engines"
                        );
                    }
                    return None;
                }
            }
        }

        // All query constraints are unsatisfiable - safe
        if self.config.verbose {
            safe_eprintln!(
                "Portfolio: Trivially safe (all {} query constraints unsatisfiable)",
                queries.len()
            );
        }

        // SOUNDNESS FIX (#6781): When BV abstraction was applied, the trivial
        // UNSAT result on the transformed problem might be due to preprocessing
        // losing reachability information (dead-param-elim + BvToBool interaction).
        // Cross-check by inlining the original problem (without BV transforms)
        // and verifying that its query constraints are also UNSAT.
        if self.bv_abstracted {
            if let Some(unsafe_result) = self.confirm_trivial_unsafe_on_original(&mut smt) {
                // Original-domain check found a SAT query — the transformed
                // UNSAT was a false negative from preprocessing.
                return Some(unsafe_result);
            }
        }

        if self.problem.predicates().is_empty() {
            if self.config.verbose {
                safe_eprintln!(
                    "Portfolio: Trivial Safe — preprocessing eliminated all {} predicates, \
                     all {} queries UNSAT, materializing original model for validation",
                    self.original_problem.predicates().len(),
                    queries.len()
                );
            }
            // The transformed problem has no predicates, so the engine-side
            // witness is empty. Back-translation reconstructs interpretations
            // for predicates eliminated by preprocessing. If that reconstructed
            // model does not verify on the original problem, fail closed and
            // let the regular engines try instead of returning a placeholder
            // Safe model (#8900).
            return self
                .accept_validated_trivial_safe(InvariantModel::new(), "predicate-free UNSAT");
        }
        let model = self.trivial_safe_candidate_model();
        self.accept_validated_trivial_safe(model, "unsat queries")
    }

    fn accept_validated_trivial_safe(
        &self,
        transformed_model: InvariantModel,
        context: &str,
    ) -> Option<PortfolioResult> {
        match self.validate_safe(&transformed_model) {
            ValidationResult::Valid => {
                let mut original_model = self.back_translator.translate_validity(transformed_model);
                self.complete_unreferenced_predicate_interpretations(&mut original_model);
                Some(PortfolioResult::Safe(original_model))
            }
            ValidationResult::Invalid(reason) => {
                if self.config.verbose {
                    safe_eprintln!(
                        "Portfolio: Trivial Safe ({context}) failed validation: {reason}; falling through to engines"
                    );
                }
                None
            }
        }
    }

    /// Confirm a trivial-unsafe result by inlining the original (un-abstracted)
    /// problem and checking query constraints in the native BV domain.
    ///
    /// When BV-to-Int abstraction makes the trivial SAT check unreliable, we
    /// can still confirm unsafety by inlining the original problem (no BV
    /// transforms, just local-var-elim + dead-param-elim + clause inlining)
    /// and checking the resulting query constraints. If the original domain
    /// also yields SAT on a query, the system is genuinely unsafe.
    ///
    /// Part of #6781: without this, the trivial-SAT result is discarded and
    /// engines fall back to the original BV problem, which they cannot solve.
    ///
    /// Also used by the non-BV trivial-Unsafe path whenever the preprocessing
    /// transform stack is non-identity (rank-6 review must-fix A): a trivial
    /// SAT on the TRANSFORMED problem is only trusted after this
    /// original-clause confirmation.
    fn confirm_trivial_unsafe_on_original(&self, smt: &mut SmtContext) -> Option<PortfolioResult> {
        // Inline the original problem without BV transforms
        let inlining_pipeline = TransformationPipeline::new()
            .with(LocalVarEliminator::new())
            .with(DeadParamEliminator::new())
            .with(ClauseInliner::new());
        let inlined = inlining_pipeline.transform(self.original_problem.clone());

        // Check if inlining eliminated all predicates
        let has_body_predicates = inlined
            .problem
            .clauses()
            .iter()
            .any(|c| !c.body.predicates.is_empty());
        if has_body_predicates {
            if self.config.verbose {
                safe_eprintln!(
                    "Portfolio: Original problem still has predicates after inlining — \
                     cannot confirm trivially"
                );
            }
            return None;
        }

        // Check query constraints in the native BV domain
        for query in inlined.problem.queries() {
            let constraint = query.body.constraint.clone().unwrap_or(ChcExpr::Bool(true));
            smt.reset();
            match smt.check_sat(&constraint) {
                SmtResult::Sat(_) => {
                    if self.config.verbose {
                        safe_eprintln!(
                            "Portfolio: Trivially unsafe confirmed in original BV domain"
                        );
                    }
                    return Some(PortfolioResult::Unsafe(Counterexample {
                        steps: Vec::new(),
                        witness: None,
                        ground_derivation: None,
                    }));
                }
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                    // This query is unreachable in original domain, continue
                }
                SmtResult::Unknown => {
                    // Can't determine in original domain
                    if self.config.verbose {
                        safe_eprintln!("Portfolio: Original-domain query check returned Unknown");
                    }
                    return None;
                }
            }
        }

        // All original queries are UNSAT — the abstracted SAT was indeed spurious
        None
    }

    pub(super) fn trivial_true_model(&self) -> InvariantModel {
        let mut model = InvariantModel::new();
        for pred in self.problem.predicates() {
            let vars: Vec<ChcVar> = pred
                .arg_sorts
                .iter()
                .enumerate()
                .map(|(i, sort)| ChcVar::new(format!("x{i}"), sort.clone()))
                .collect();
            model.set(
                pred.id,
                PredicateInterpretation::new(vars, ChcExpr::Bool(true)),
            );
        }
        model
    }

    fn trivial_safe_candidate_model(&self) -> InvariantModel {
        if self.problem.predicates().is_empty() {
            InvariantModel::new()
        } else {
            self.trivial_true_model()
        }
    }
}
