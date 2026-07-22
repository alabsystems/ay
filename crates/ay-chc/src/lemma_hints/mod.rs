// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Lemma Hint Provider Interface
//!
//! This module defines a trait for pluggable domain-specific lemma/invariant hints
//! that can be injected into the PDR solving loop. Hints are candidate invariants
//! that are validated via `is_inductive_blocking()` before insertion.
//!
//! # Architecture
//!
//! - Providers produce candidate invariant formulas per predicate
//! - Hints are validated through existing inductiveness checking
//! - Integration happens after forward discovery in `PdrSolver::solve()`
//!
//! # Performance
//!
//! - Static registration via compiled-in providers (no dynamic loading)
//! - No SMT calls in providers; validation happens in core
//! - Deterministic ordering via priority + predicate ID + formula string
//!
//! # Safety
//!
//! Hints are never trusted. A hint that fails inductiveness/init checks is dropped.

mod bool_parity;
mod bounds_from_init;
mod mod_arithmetic;
mod parametric_mul;
mod parametric_mul_collect;
mod recurrence_conserved;
#[cfg(test)]
mod tests;

use crate::expr::{ChcExpr, ChcOp, ChcVar};
use crate::predicate::PredicateId;
use crate::problem::ChcProblem;
use std::sync::Arc;

pub(crate) use recurrence_conserved::RecurrenceConservedEqualityProvider;

use bool_parity::BOOL_MOD_PARITY_PROVIDER;
use bounds_from_init::BOUNDS_FROM_INIT_PROVIDER;
use mod_arithmetic::{MOD_RESIDUE_PROVIDER, MOD_SUM_PROVIDER};
use parametric_mul_collect::PARAMETRIC_MULTIPLICATION_PROVIDER;
use recurrence_conserved::RECURRENCE_CONSERVED_EQ_PROVIDER;

/// Stage at which hints are collected.
///
/// External providers can use this to vary their behavior between
/// solver startup (initial hint injection) and stuck recovery.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum HintStage {
    /// Called once during solver startup (after internal forward discovery)
    Startup,
    /// Called only when solver is stuck (optional follow-up)
    Stuck,
}

/// Request context provided to hint providers.
///
/// Contains the CHC problem being solved and access to canonical variables
/// for each predicate. External providers use this to construct hint formulas
/// over the correct variable names.
pub struct HintRequest<'a> {
    /// Stage of hint collection
    pub stage: HintStage,
    /// The CHC problem being solved
    pub problem: &'a ChcProblem,
    /// Access to canonical vars for a predicate
    ///
    /// Hint formulas should be expressed in these vars to avoid rewriting.
    /// Returns None if predicate ID is invalid.
    canonical_vars_fn: &'a dyn Fn(PredicateId) -> Option<&'a [ChcVar]>,
}

impl<'a> HintRequest<'a> {
    /// Create a new hint request
    pub(crate) fn new(
        stage: HintStage,
        problem: &'a ChcProblem,
        canonical_vars_fn: &'a dyn Fn(PredicateId) -> Option<&'a [ChcVar]>,
    ) -> Self {
        Self {
            stage,
            problem,
            canonical_vars_fn,
        }
    }

    /// Get canonical variables for a predicate.
    ///
    /// Returns the canonical variable names used internally by the PDR solver
    /// for the given predicate. Hint formulas must be expressed over these
    /// variables for the solver to use them without renaming.
    pub fn canonical_vars(&self, pred: PredicateId) -> Option<&'a [ChcVar]> {
        (self.canonical_vars_fn)(pred)
    }

    /// Create a minimal HintRequest for unit tests that don't need
    /// canonical variables or problem context.
    #[cfg(test)]
    pub(crate) fn empty_for_test() -> HintRequest<'static> {
        use std::sync::LazyLock;
        static EMPTY_PROBLEM: LazyLock<ChcProblem> = LazyLock::new(ChcProblem::new);
        HintRequest {
            stage: HintStage::Startup,
            problem: &EMPTY_PROBLEM,
            canonical_vars_fn: &|_| None,
        }
    }
}

fn arithmetic_providers_applicable(problem: &ChcProblem) -> bool {
    // The arithmetic providers synthesize numeric equalities, modular facts,
    // and multiplication relationships. After #5877's BV-to-Bool
    // preprocessing, some CHC problems become pure-Boolean with hundreds of
    // predicate arguments. Walking those giant Boolean formulas to discover
    // numeric hints is pure startup overhead and can exceed the advertised
    // non-fixpoint budget before PDR reaches its main loop.
    problem.predicates().iter().any(|pred| {
        pred.arg_sorts
            .iter()
            .any(|sort| !matches!(sort, crate::ChcSort::Bool))
    })
}

/// A candidate lemma hint
#[derive(Debug, Clone)]
pub struct LemmaHint {
    /// The predicate this hint applies to
    pub predicate: PredicateId,
    /// The invariant formula (must be over canonical vars for the predicate)
    pub formula: ChcExpr,
    /// Priority for deterministic ordering (lower = higher priority)
    pub priority: u16,
    /// Source identifier for debugging (e.g., "bounds-discovery-v1")
    pub source: &'static str,
}

impl LemmaHint {
    /// Create a new lemma hint
    pub fn new(
        predicate: PredicateId,
        formula: ChcExpr,
        priority: u16,
        source: &'static str,
    ) -> Self {
        Self {
            predicate,
            formula,
            priority,
            source,
        }
    }
}

/// Trait for providing domain-specific lemma hints.
///
/// Implementations must be `Send + Sync` to allow parallel hint collection.
/// Providers must produce deterministic output for the same input.
///
/// # External Usage
///
/// External consumers (e.g., model-checker-consumer) can implement this trait to provide
/// domain-specific invariant hints dynamically. Register runtime providers
/// via `PdrConfig::with_user_hint_providers` or
/// `PortfolioConfig::set_pdr_user_hint_providers`.
///
/// Hints are never trusted — all candidates are validated via SMT
/// inductiveness checks before acceptance.
pub trait LemmaHintProvider: Send + Sync {
    /// Collect hints for the given request.
    ///
    /// Providers should push candidate hints to `out`. The order within
    /// a single provider's output doesn't matter; hints are sorted
    /// deterministically by the core before validation.
    ///
    /// Providers should NOT make SMT calls — hints are validated by the core.
    fn collect(&self, req: &HintRequest<'_>, out: &mut Vec<LemmaHint>);
}

// ============================================================================
// Provider Registry
// ============================================================================

/// Built-in providers that remain useful even on pure-Boolean predicates.
///
/// This is a static slice of providers for zero-overhead registration.
/// Providers are registered at compile time via this constant.
static ALWAYS_ON_HINT_PROVIDERS: &[&dyn LemmaHintProvider] = &[&BOUNDS_FROM_INIT_PROVIDER];

/// Built-in providers that only matter when predicate state has numeric sorts.
static ARITHMETIC_HINT_PROVIDERS: &[&dyn LemmaHintProvider] = &[
    &RECURRENCE_CONSERVED_EQ_PROVIDER,
    &PARAMETRIC_MULTIPLICATION_PROVIDER,
    &MOD_RESIDUE_PROVIDER,
    &MOD_SUM_PROVIDER,
    &BOOL_MOD_PARITY_PROVIDER,
];

/// Collect hints from all registered providers plus extra runtime hints.
///
/// Returns hints sorted deterministically by (priority, predicate_id, formula).
/// Duplicate hints (same predicate and formula) are removed.
///
/// # Arguments
/// * `req` - Hint request containing problem context
/// * `extra` - Additional runtime hints (e.g., from model-checker-consumer loop invariants)
#[cfg(test)]
pub(crate) fn collect_all_hints_with_extra(
    req: &HintRequest<'_>,
    extra: &[LemmaHint],
) -> Vec<LemmaHint> {
    collect_all_hints_with_extra_providers(req, &[], extra)
}

/// Collect hints from all registered providers, runtime providers, and extra hints.
///
/// Merges three hint sources:
/// 1. Built-in always-on providers (`ALWAYS_ON_HINT_PROVIDERS`)
/// 2. Built-in arithmetic providers (`ARITHMETIC_HINT_PROVIDERS`)
/// 3. Runtime providers (`extra_providers`) — user-registered `LemmaHintProvider` impls
/// 4. Runtime hints (`extra_hints`) — pre-computed `LemmaHint` values
///
/// Returns hints sorted deterministically by (priority, predicate_id, formula).
/// Duplicate hints (same predicate and formula) are removed.
pub(crate) fn collect_all_hints_with_extra_providers(
    req: &HintRequest<'_>,
    extra_providers: &[Arc<dyn LemmaHintProvider>],
    extra_hints: &[LemmaHint],
) -> Vec<LemmaHint> {
    let mut hints = Vec::new();

    for provider in ALWAYS_ON_HINT_PROVIDERS {
        provider.collect(req, &mut hints);
    }

    // Skip arithmetic-heavy built-ins on pure-Boolean problems (notably
    // BV-to-Bool-expanded CHC) to avoid spending most of the startup budget
    // traversing large Boolean formulas for numeric hints that cannot apply.
    if arithmetic_providers_applicable(req.problem) {
        for provider in ARITHMETIC_HINT_PROVIDERS {
            provider.collect(req, &mut hints);
        }
    }

    // Collect from runtime providers
    for provider in extra_providers {
        provider.collect(req, &mut hints);
    }

    // Add runtime hints
    hints.extend(extra_hints.iter().cloned());

    // Sort deterministically for reproducibility
    hints.sort_by(|a, b| {
        a.priority
            .cmp(&b.priority)
            .then_with(|| a.predicate.0.cmp(&b.predicate.0))
            .then_with(|| a.formula.cmp(&b.formula))
    });

    // Deduplicate: remove consecutive hints with same predicate and formula
    hints.dedup_by(|a, b| a.predicate == b.predicate && a.formula == b.formula);

    hints
}

/// Check if any hint providers are registered (static or runtime)
pub(crate) fn has_providers() -> bool {
    !(ALWAYS_ON_HINT_PROVIDERS.is_empty() && ARITHMETIC_HINT_PROVIDERS.is_empty())
}

// ============================================================================
// Runtime Provider Container
// ============================================================================

/// Container for runtime (dynamically registered) hint providers.
///
/// Wraps `Vec<Arc<dyn LemmaHintProvider>>` to allow `PdrConfig` to remain
/// `Debug + Clone` without requiring providers to implement `Debug`.
#[derive(Clone, Default)]
pub struct HintProviders(pub Vec<Arc<dyn LemmaHintProvider>>);

impl std::fmt::Debug for HintProviders {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "HintProviders({} providers)", self.0.len())
    }
}

// ============================================================================
// Canonical Variable Helpers
// ============================================================================

/// Canonical variable name used by the PDR solver for a predicate argument.
///
/// The naming convention is `__p{pred_index}_a{arg_index}`. External tools
/// (e.g., model-checker-consumer) should use this function to construct hint formulas that
/// match the solver's internal variable naming.
pub fn canonical_var_name(pred: PredicateId, arg_idx: usize) -> String {
    format!("__p{}_a{}", pred.index(), arg_idx)
}

/// Canonical variable for a specific predicate argument.
///
/// Returns `None` if `pred` is not a valid predicate in `problem` or if
/// `arg_idx` is out of bounds for the predicate's argument list.
pub fn canonical_var_for_pred_arg(
    problem: &ChcProblem,
    pred: PredicateId,
    arg_idx: usize,
) -> Option<ChcVar> {
    let predicate = problem.get_predicate(pred)?;
    let sort = predicate.arg_sorts.get(arg_idx)?;
    Some(ChcVar::new(canonical_var_name(pred, arg_idx), sort.clone()))
}

/// Canonical variables for all arguments of a predicate.
///
/// Returns `None` if `pred` is not a valid predicate in `problem`.
/// The returned variables use the naming convention `__p{pred_index}_a{i}`
/// and carry the sorts from the predicate declaration.
pub fn canonical_vars_for_pred(problem: &ChcProblem, pred: PredicateId) -> Option<Vec<ChcVar>> {
    let predicate = problem.get_predicate(pred)?;
    Some(
        predicate
            .arg_sorts
            .iter()
            .enumerate()
            .map(|(i, sort)| ChcVar::new(canonical_var_name(pred, i), sort.clone()))
            .collect(),
    )
}
