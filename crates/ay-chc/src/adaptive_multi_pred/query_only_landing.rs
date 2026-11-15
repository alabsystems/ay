// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! A satisfiable collapsed query lands through its own model.
//!
//! When preprocessing inlines every predicate of an acyclic problem away,
//! `discharge_preprocessed_query_only_problem` decides each collapsed query
//! body directly. A `sat` body is a counterexample candidate. Before this
//! landing its only route to a verdict was the bounded replay on the original
//! clauses (`BmcSolver::replay_confirm_unsafe_on_problem`). That replay
//! starts from scratch and takes the original paths one at a time in clause
//! order, so its cost grows with the position of the satisfiable path. On
//! model-checker-consumer's realloc-grow twin (39 error rules, 25 paths) the replay needed
//! about 8 s when the failing assertion's path was #12 and 27 s when it was
//! last, past the probe's 15 s grant, so the same clause set was `unsafe` or
//! `unknown` depending on rule order.
//!
//! [`AdaptivePortfolio::land_query_only_model`] reuses the model the discharge
//! already has instead:
//!
//! 1. The discharge decides the body after `simplify_constants` and
//!    per-disjunct definition elimination, so its model names only the
//!    variables that survived. Each disjunct is eliminated again, now with
//!    its trail; the first one the model makes true has its definitions
//!    evaluated back (`ChcExpr::extend_model_by_definitions`). This is pure
//!    evaluation.
//! 2. The extended model, completed for the collapsed clause, is a one-step
//!    ground derivation over the TRANSFORMED problem. It must validate
//!    there, which is a cheap early refusal.
//! 3. `ground_backtranslate_landing` maps it through every pass of the chain
//!    and accepts only what ground-validates on the ORIGINAL clauses.
//!
//! The accepted derivation is validated again downstream. Every failure
//! returns `None`, and the replay then runs as before. The landing gets at
//! most half of what remains of the discharge's window, so a refused landing
//! leaves the replay at least the other half.

use crate::adaptive::AdaptivePortfolio;
use crate::ground_derivation::{
    complete::complete_env_for_clause, validate_ground_derivation, GroundDerivation,
    GroundDerivationStep,
};
use crate::pdr::Counterexample;
use crate::portfolio::PortfolioResult;
use crate::smt::SmtValue;
use crate::transform::BackTranslator;
use crate::{CancellationToken, ChcExpr, ChcOp, ChcProblem, HornClause};
use ay_core::kani_compat::DetHashMap as FxHashMap;
use ay_core::time::Instant;

#[cfg(test)]
thread_local! {
    /// Counterexamples this thread's query-only landing accepted (tests).
    static LANDED: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// Counterexamples this thread's query-only landing has accepted (tests).
#[cfg(test)]
pub(crate) fn query_only_landings() -> usize {
    LANDED.with(std::cell::Cell::get)
}

impl AdaptivePortfolio {
    /// Turn `model`, a model of the simplified body of `query` (a collapsed
    /// query-only clause of `problem`), into a counterexample of the ORIGINAL
    /// problem through `back_translator`. `None` unless the derivation
    /// ground-validates on the original clauses within the window.
    pub(super) fn land_query_only_model(
        &self,
        problem: &ChcProblem,
        query: &HornClause,
        model: &FxHashMap<String, SmtValue>,
        back_translator: &dyn BackTranslator,
        label: &'static str,
        deadline: Instant,
        cancellation: &CancellationToken,
    ) -> Option<Counterexample> {
        if !crate::ground_derivation::ground_backtranslation_enabled() {
            return None;
        }
        let now = Instant::now();
        let deadline = now + deadline.saturating_duration_since(now) / 2;
        let open = || {
            !self.cancellation_token.is_cancelled()
                && !cancellation.is_cancelled()
                && Instant::now() < deadline
        };
        let _smt_deadline = crate::smt::ScopedSmtDeadline::install_until(deadline);
        let _witness_budget =
            crate::ground_derivation::witness::ScopedWitnessChainBudget::new_bounded(
                Some(deadline),
                cancellation.clone(),
            );
        let clause_index = problem
            .clauses()
            .iter()
            .position(|clause| std::ptr::eq(clause, query))?;
        let constraint = query.body.constraint.clone().unwrap_or(ChcExpr::Bool(true));
        let extended = extend_by_satisfied_disjunct(&constraint, model);
        if !open() {
            return None;
        }
        let mut env: FxHashMap<String, SmtValue> = query
            .body
            .vars()
            .into_iter()
            .filter_map(|var| Some((var.name.clone(), extended.get(&var.name)?.clone())))
            .collect();
        if !complete_env_for_clause(query, &mut env) || !open() {
            return None;
        }
        let transformed = GroundDerivation {
            steps: vec![GroundDerivationStep {
                clause_index,
                env,
                premises: Vec::new(),
            }],
            query_step: 0,
        };
        if let Err(err) = validate_ground_derivation(problem, &transformed) {
            tracing::debug!(
                "Adaptive: {label} query-only model does not ground-validate on the collapsed \
                 clause ({err}); replaying on original clauses"
            );
            return None;
        }
        if !open() {
            return None;
        }
        let candidate = Counterexample::new(Vec::new()).with_ground_derivation(transformed);
        let (PortfolioResult::Unsafe(landed), _) = self.ground_backtranslate_landing(
            &candidate,
            back_translator,
            "Adaptive",
            self.config.verbose,
            Some(deadline),
            cancellation,
        )?
        else {
            return None;
        };
        // Publish the trace the validated derivation derives: the candidate
        // claimed none.
        let landed = landed
            .ground_derivation
            .as_ref()
            .and_then(|derivation| Counterexample::traced_by_derivation(&self.problem, derivation))
            .unwrap_or(landed);
        if !open() {
            return None;
        }
        #[cfg(test)]
        LANDED.with(|landed| landed.set(landed.get() + 1));
        Some(landed)
    }
}

/// `model` extended to the variables that definition elimination removed
/// from the first disjunct of `constraint` (after `simplify_constants`, as
/// the discharge decided it) whose eliminated form `model` makes true; a copy
/// of `model` when no disjunct qualifies.
///
/// Every value comes from evaluating a definition's right-hand side, and the
/// derivation built from it is still decided by ground validation.
fn extend_by_satisfied_disjunct(
    constraint: &ChcExpr,
    model: &FxHashMap<String, SmtValue>,
) -> FxHashMap<String, SmtValue> {
    let body = constraint.simplify_constants();
    let disjuncts: Vec<&ChcExpr> = match &body {
        ChcExpr::Op(ChcOp::Or, args) => args.iter().map(AsRef::as_ref).collect(),
        other => vec![other],
    };
    for disjunct in disjuncts {
        if crate::smt::smt_deadline_expired() {
            break;
        }
        let (eliminated, definitions) = disjunct.eliminate_top_level_definitions_with_trail();
        if matches!(
            crate::expr::evaluate_expr(&eliminated, model),
            Some(SmtValue::Bool(true))
        ) {
            let mut extended = model.clone();
            ChcExpr::extend_model_by_definitions(&definitions, &mut extended);
            return extended;
        }
    }
    model.clone()
}

#[cfg(test)]
mod tests;
