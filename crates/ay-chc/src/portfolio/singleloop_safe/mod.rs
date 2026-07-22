// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared SingleLoop Safe witness translation adapter.
//!
//! Both TPA and TRL produce Safe witnesses for SingleLoop-encoded
//! multi-predicate problems. This module provides the shared translation
//! pipeline: reverse canonicalization, back-translation, alien-variable
//! elimination, and InvariantModel construction.
//!
//! Extracted from `engines.rs` to give the raw-witness fix (#7170) a
//! clean landing zone. See the development design notes.

use crate::mbp::Mbp;
use crate::pdr::model::{InvariantModel, InvariantVerificationMethod, PredicateInterpretation};
use crate::single_loop::SingleLoopTransformation;
use crate::smt::SmtContext;
use crate::{ChcExpr, ChcProblem, ChcVar};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};
use tracing::warn;

/// A state-space witness from a SingleLoop engine (TPA or TRL).
///
/// Represents an invariant over the SingleLoop canonical state variables
/// (v0, v1, ...) before back-translation to per-predicate interpretations.
/// Both TPA and TRL produce this intermediate form; the shared adapter
/// then translates it to the final `InvariantModel`.
pub(crate) struct SingleLoopSafeWitness {
    /// The state-space invariant formula over original state variables.
    pub(crate) formula: ChcExpr,
    /// Verification method to propagate to the final model.
    pub(crate) verification_method: InvariantVerificationMethod,
    /// Whether the invariant was proven individually inductive.
    pub(crate) individually_inductive: bool,
}

impl SingleLoopSafeWitness {
    /// Build a witness from a TPA Safe result.
    ///
    /// TPA produces a raw state-space invariant over canonical `v{i}` variables
    /// that needs reverse canonicalization to the original state variable names.
    pub(crate) fn from_tpa(inv_expr: &ChcExpr, state_vars: &[ChcVar]) -> Self {
        let reverse_canonical: Vec<(ChcVar, ChcExpr)> = state_vars
            .iter()
            .enumerate()
            .map(|(i, sv)| {
                let canonical = ChcVar::new(format!("v{i}"), sv.sort.clone());
                (canonical, ChcExpr::var(sv.clone()))
            })
            .collect();
        let original_space_inv = inv_expr.substitute(&reverse_canonical);
        Self {
            formula: original_space_inv,
            verification_method: InvariantVerificationMethod::TpaInterpolation,
            individually_inductive: false,
        }
    }

    /// Build a witness from a TRL Safe result.
    ///
    /// TRL Safe models reach this adapter in two shapes:
    ///
    /// 1. Older remapped models with synthetic `__p{pred}_a{i}` variables.
    /// 2. Expanded-system models whose variables already match `state_vars`.
    ///
    /// In both cases the adapter reconstructs the state-space invariant over
    /// the SingleLoop canonical state variables so the shared back-translation
    /// path can recover per-predicate interpretations.
    pub(crate) fn from_trl(model: &InvariantModel, state_vars: &[ChcVar]) -> Option<Self> {
        if model.len() != 1 {
            return None;
        }
        let (_, interp) = model.iter().next()?;
        if interp.vars.len() != state_vars.len() {
            return None;
        }
        if interp
            .vars
            .iter()
            .zip(state_vars.iter())
            .any(|(interp_var, state_var)| interp_var.sort != state_var.sort)
        {
            return None;
        }
        if !formula_is_closed_over(&interp.formula, &interp.vars) {
            warn!(
                event = "chc_singleloop_trl_unbound_witness_var",
                "TRL SingleLoop Safe witness contained variables outside its binders; failing closed"
            );
            return None;
        }
        let reverse_canonical: Vec<(ChcVar, ChcExpr)> = interp
            .vars
            .iter()
            .cloned()
            .zip(state_vars.iter().cloned().map(ChcExpr::var))
            .collect();
        let formula = interp
            .formula
            .substitute(&reverse_canonical)
            .simplify_constants();
        Some(Self {
            formula,
            verification_method: model.verification_method,
            individually_inductive: model.individually_inductive,
        })
    }
}

/// Translate a SingleLoop state-space witness to a multi-predicate `InvariantModel`.
///
/// Performs:
/// 1. Back-translation via `SingleLoopTransformation::back_translate_invariant`
/// 2. Simplification
/// 3. Alien-variable closure check + AllSAT/MBP elimination
/// 4. Variable renaming to PDR canonical form (`__p{pred}_a{i}`)
///
/// Returns `None` if back-translation or alien-variable elimination fails.
pub(crate) fn translate_singleloop_safe(
    problem: &ChcProblem,
    tx: &SingleLoopTransformation,
    witness: &SingleLoopSafeWitness,
) -> Option<InvariantModel> {
    let mut simplified_interps: FxHashMap<_, _> = tx
        .back_translate_invariant(&witness.formula)
        .into_iter()
        .map(|(pred, formula)| (pred, formula.simplify_constants()))
        .collect();

    // Check if interps are already closed (no alien vars)
    if !interps_are_closed(problem, &simplified_interps) {
        // Alien variables detected — eliminate via AllSAT + MBP (Golem's approach).
        if !eliminate_alien_vars(problem, &mut simplified_interps) {
            return None;
        }
    }

    let mut model = build_multi_pred_model(problem, &simplified_interps)?;
    model.verification_method = witness.verification_method;
    model.individually_inductive = witness.individually_inductive;
    Some(model)
}

/// Build an `InvariantModel` from multi-predicate interpretations
/// produced by SingleLoop back-translation.
///
/// Renames `v0, v1, ...` to PDR canonical vars `__p{pred}_a{i}`.
fn build_multi_pred_model(
    problem: &ChcProblem,
    interps: &FxHashMap<crate::PredicateId, ChcExpr>,
) -> Option<InvariantModel> {
    let mut model = InvariantModel::new();
    for pred in problem.predicates() {
        if let Some(formula) = interps.get(&pred.id) {
            let pdkind_vars: Vec<_> = pred
                .arg_sorts
                .iter()
                .enumerate()
                .map(|(i, sort)| ChcVar::new(format!("v{i}"), sort.clone()))
                .collect();
            let pdr_vars: Vec<_> = pred
                .arg_sorts
                .iter()
                .enumerate()
                .map(|(i, sort)| {
                    ChcVar::new(format!("__p{}_a{}", pred.id.index(), i), sort.clone())
                })
                .collect();
            let subst: Vec<(ChcVar, ChcExpr)> = pdkind_vars
                .into_iter()
                .zip(pdr_vars.iter().cloned().map(ChcExpr::var))
                .collect();
            let renamed = formula.substitute(&subst).simplify_constants();
            if !formula_is_closed_over(&renamed, &pdr_vars) {
                warn!(
                    event = "chc_singleloop_translated_unbound_var",
                    predicate = pred.id.index(),
                    "SingleLoop Safe back-translation left variables outside the predicate binders; failing closed"
                );
                return None;
            }
            model.set(pred.id, PredicateInterpretation::new(pdr_vars, renamed));
        }
    }
    Some(model)
}

fn formula_is_closed_over(formula: &ChcExpr, allowed: &[ChcVar]) -> bool {
    let allowed: FxHashSet<ChcVar> = allowed.iter().cloned().collect();
    formula.vars().into_iter().all(|var| allowed.contains(&var))
}

/// Check whether all back-translated interpretations are closed
/// (contain only the predicate's own `v{i}` variables).
fn interps_are_closed(
    problem: &ChcProblem,
    interps: &FxHashMap<crate::PredicateId, ChcExpr>,
) -> bool {
    problem.predicates().iter().all(|pred| {
        let Some(formula) = interps.get(&pred.id) else {
            return false;
        };
        let allowed: FxHashSet<ChcVar> = pred
            .arg_sorts
            .iter()
            .enumerate()
            .map(|(i, sort)| ChcVar::new(format!("v{i}"), sort.clone()))
            .collect();
        formula.vars().into_iter().all(|var| allowed.contains(&var))
    })
}

/// Eliminate alien variables from back-translated invariants using
/// AllSAT + MBP enumeration, following Golem's `QuantifierElimination::eliminate`.
///
/// For each predicate's back-translated invariant, alien variables are variables
/// belonging to other predicates that weren't simplified away. The semantics
/// require universal closure: the invariant must hold for ALL values of alien
/// variables. This is computed as `not(exists alien. not(inv))`.
///
/// Reference: `reference/golem/src/transformers/SingleLoopTransformation.cc:144-157`
/// Reference: `reference/golem/src/QuantifierElimination.cc:15-41`
fn eliminate_alien_vars(
    problem: &ChcProblem,
    interps: &mut FxHashMap<crate::PredicateId, ChcExpr>,
) -> bool {
    let mbp = Mbp::new();

    for pred in problem.predicates() {
        let Some(formula) = interps.get(&pred.id) else {
            return false;
        };

        let pred_vars: FxHashSet<ChcVar> = pred
            .arg_sorts
            .iter()
            .enumerate()
            .map(|(i, sort)| ChcVar::new(format!("v{i}"), sort.clone()))
            .collect();

        let alien_vars: Vec<ChcVar> = formula
            .vars()
            .into_iter()
            .filter(|v| !pred_vars.contains(v))
            .collect();

        if alien_vars.is_empty() {
            continue;
        }

        // Universal QE: forall alien. inv = not(exists alien. not(inv))
        let negated = ChcExpr::not(formula.clone());
        let keep_vars: Vec<ChcVar> = pred_vars.into_iter().collect();

        let mut smt = SmtContext::new();
        let mut projections = Vec::new();
        let mut blocking = negated.clone();

        const MAX_ALLSAT_ITERS: usize = 50;
        let mut hit_cap = false;
        for iter in 0..MAX_ALLSAT_ITERS {
            match smt.get_model(&blocking) {
                Some(model) => {
                    let projection = mbp.keep_only(&negated, &keep_vars, &model);
                    projections.push(projection.clone());
                    blocking = ChcExpr::and(blocking, ChcExpr::not(projection));
                    if iter + 1 == MAX_ALLSAT_ITERS {
                        hit_cap = true;
                    }
                }
                None => break,
            }
        }
        if hit_cap {
            warn!(
                event = "chc_singleloop_allsat_cap_hit",
                cap = MAX_ALLSAT_ITERS,
                iterations_completed = projections.len(),
                "AllSAT iteration cap reached during alien-variable elimination; \
                 invariant may be incomplete, which can weaken PDR convergence"
            );
        }

        let exists_neg = if projections.is_empty() {
            ChcExpr::Bool(false)
        } else {
            ChcExpr::or_all(projections)
        };

        let cleaned = ChcExpr::not(exists_neg).simplify_constants();

        let keep_set: FxHashSet<&ChcVar> = keep_vars.iter().collect();
        let has_remaining_aliens = cleaned.vars().into_iter().any(|v| !keep_set.contains(&v));
        if has_remaining_aliens {
            return false;
        }

        interps.insert(pred.id, cleaned);
    }

    true
}

#[cfg(test)]
mod tests;
