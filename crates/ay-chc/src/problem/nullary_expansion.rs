// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The clause correspondence of
//! [`ChcProblem::expand_nullary_fail_queries`] and the ground-derivation
//! translation back through it.
//!
//! The expansion rewrites `body ⇒ fail` / `fail ⇒ false` into the query
//! `body ⇒ false` (only for an unconstrained `fail ⇒ false`: dropping a
//! constraint `φ` would be exact only when `φ` holds), drops both originals
//! and appends the new queries, so clause
//! indices move and one input derivation step (the `fail ⇒ false` query) has
//! no counterpart. A PDR engine searches the expanded problem, but its caller
//! validates the answer on the problem it handed over: a ground derivation over
//! the expanded clauses is re-indexed here, and a root on an expanded query
//! becomes the step through `body ⇒ fail` followed by the `fail ⇒ false`
//! query. The result is re-validated
//! against the input problem; any mismatch drops it (fail closed).

use super::ChcProblem;
use crate::ground_derivation::complete::complete_env_for_clause;
use crate::ground_derivation::{
    validate_ground_derivation_with_progress, GroundDerivation, GroundDerivationError,
    GroundDerivationStep,
};
use ay_core::kani_compat::DetHashMap as FxHashMap;
use std::sync::Arc;

/// Where one clause of the expanded problem came from.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ExpandedClauseOrigin {
    /// Input clause `.0`, unchanged.
    Kept(usize),
    /// The query built from input clause `into_fail` (`body ⇒ fail`) for the
    /// input query `fail_query` (`fail ⇒ false`).
    Expanded { into_fail: usize, fail_query: usize },
}

/// The input problem of a nullary expansion and each expanded clause's origin.
#[derive(Debug, Clone)]
pub(crate) struct NullaryExpansion {
    input: Arc<ChcProblem>,
    origins: Vec<ExpandedClauseOrigin>,
}

impl NullaryExpansion {
    pub(super) fn new(input: ChcProblem, origins: Vec<ExpandedClauseOrigin>) -> Self {
        Self {
            input: Arc::new(input),
            origins,
        }
    }

    /// The origin of every clause of the expanded problem, by index.
    #[cfg(test)]
    pub(crate) fn origins(&self) -> &[ExpandedClauseOrigin] {
        &self.origins
    }

    /// The recorded pre-case-split clause surface, not the later split count.
    pub(crate) fn expanded_clause_count(&self) -> usize {
        self.origins.len()
    }

    /// The origin of clause `index` of the expanded problem.
    pub(crate) fn origin(&self, index: usize) -> Option<ExpandedClauseOrigin> {
        self.origins.get(index).copied()
    }

    /// `derivation` (over the expanded problem, before any case split:
    /// `expanded_clauses` must be `expanded_clause_count`) restated over the
    /// input problem, or `None` when it cannot be mapped or the mapped
    /// derivation does not validate there. Compatibility entrypoint with no
    /// caller-supplied stop owner.
    #[cfg(test)]
    pub(crate) fn translate_derivation(
        &self,
        derivation: &GroundDerivation,
        expanded_clauses: usize,
    ) -> Option<GroundDerivation> {
        self.translate_derivation_with_progress(derivation, expanded_clauses, &mut || true)
            .ok()
            .flatten()
    }

    /// Map and validate on the captured input under the same sticky owner.
    ///
    /// Rejection remains `Ok(None)`; refusal is terminal `Interrupted`.
    /// Environment copying/completion and individual native evaluator phases
    /// remain opaque. These observations do not establish a hard deadline or
    /// preprice the allocations of the existing translation.
    pub(crate) fn translate_derivation_with_progress(
        &self,
        derivation: &GroundDerivation,
        expanded_clauses: usize,
        progress: &mut dyn FnMut() -> bool,
    ) -> Result<Option<GroundDerivation>, GroundDerivationError> {
        let mut stopped = false;
        let mut open = || {
            if stopped {
                return false;
            }
            // Refusal (or an unwinding observer) cannot resurrect this owner.
            stopped = true;
            let allowed = progress();
            stopped = !allowed;
            allowed
        };
        if !open() {
            return Err(GroundDerivationError::Interrupted);
        }
        let translated = self.map_derivation(derivation, expanded_clauses, &mut open);
        if !open() {
            return Err(GroundDerivationError::Interrupted);
        }
        let Some(translated) = translated else {
            return Ok(None);
        };
        let result = validate_ground_derivation_with_progress(&self.input, &translated, &mut open);
        // Observe after validator temporaries have been released, before the
        // mapped proof can escape. An Interrupted result stays sticky.
        if !open() {
            return Err(GroundDerivationError::Interrupted);
        }
        match result {
            Ok(()) => Ok(Some(translated)),
            Err(GroundDerivationError::Interrupted) => Err(GroundDerivationError::Interrupted),
            Err(err) => {
                tracing::debug!(%err, "nullary expansion: restated derivation rejected");
                Ok(None)
            }
        }
    }

    fn map_derivation(
        &self,
        derivation: &GroundDerivation,
        expanded_clauses: usize,
        progress: &mut dyn FnMut() -> bool,
    ) -> Option<GroundDerivation> {
        if expanded_clauses != self.origins.len() || !progress() {
            return None;
        }
        let clauses = self.input.clauses();
        let capacity = derivation.len().checked_add(1)?;
        let mut steps: Vec<GroundDerivationStep> = Vec::with_capacity(capacity);
        let mut placed: Vec<usize> = Vec::with_capacity(derivation.len());
        let mut query_step = None;
        for (index, step) in derivation.steps.iter().enumerate() {
            if !progress() {
                return None;
            }
            let mut premises = Vec::with_capacity(step.premises.len());
            for premise in &step.premises {
                if !progress() {
                    return None;
                }
                premises.push(*placed.get(*premise)?);
            }
            let origin = *self.origins.get(step.clause_index)?;
            if !progress() {
                return None;
            }
            let env = step.env.clone();
            if !progress() {
                return None;
            }
            let at = steps.len();
            match origin {
                ExpandedClauseOrigin::Kept(clause_index) => steps.push(GroundDerivationStep {
                    clause_index,
                    env,
                    premises,
                }),
                ExpandedClauseOrigin::Expanded {
                    into_fail,
                    fail_query,
                } => {
                    if index != derivation.query_step {
                        return None;
                    }
                    steps.push(GroundDerivationStep {
                        clause_index: into_fail,
                        env,
                        premises,
                    });
                    let mut env = FxHashMap::default();
                    if !progress() {
                        return None;
                    }
                    let completed = complete_env_for_clause(clauses.get(fail_query)?, &mut env);
                    if !progress() || !completed {
                        return None;
                    }
                    query_step = Some(steps.len());
                    steps.push(GroundDerivationStep {
                        clause_index: fail_query,
                        env,
                        premises: vec![at],
                    });
                }
            }
            if index == derivation.query_step && query_step.is_none() {
                query_step = Some(at);
            }
            placed.push(at);
            if !progress() {
                return None;
            }
        }
        drop(placed);
        if !progress() {
            return None;
        }
        Some(GroundDerivation {
            steps,
            query_step: query_step?,
        })
    }
}

#[cfg(test)]
mod tests;
