// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Concrete reachability facts with justification chains.
//!
//! This mirrors Z3 Spacer's `reach_fact` concept: under-approximations of reachable
//! states that can be linked into a derivation DAG for counterexample reconstruction.

use crate::smt::SmtValue;
use crate::{ChcExpr, PredicateId};
use ay_core::kani_compat::DetHashMap as FxHashMap;

/// Hard cap on retained reach facts.
pub(crate) const MAX_REACH_FACTS: usize = 100_000;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct ReachFactId(pub(crate) usize);

#[derive(Debug, Clone)]
pub(crate) struct ReachFact {
    pub(crate) id: ReachFactId,
    pub(crate) predicate: PredicateId,
    /// Number of transition steps from init used to derive this fact.
    pub(crate) level: usize,
    /// Concrete fact over canonical predicate variables.
    pub(crate) state: ChcExpr,
    /// Clause index (in `ChcProblem::clauses()`) used to derive this fact.
    pub(crate) incoming_clause: Option<usize>,
    /// Premise reach facts used in the derivation (body predicates).
    pub(crate) premises: Vec<ReachFactId>,
    /// Concrete instances from the SMT model witnessing this derivation step.
    pub(crate) instances: FxHashMap<String, SmtValue>,
}

#[derive(Debug, Clone, Default)]
pub(crate) struct ReachFactStore {
    facts: Vec<ReachFact>,
    by_pred_level: FxHashMap<(PredicateId, usize), Vec<ReachFactId>>,
    saturated: bool,
}

impl ReachFactStore {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    pub(crate) fn max_facts() -> usize {
        MAX_REACH_FACTS
    }

    fn add_with_cap(&mut self, mut fact: ReachFact, cap: usize) -> Option<ReachFactId> {
        if self.facts.len() >= cap {
            if !self.saturated {
                tracing::warn!(
                    cap,
                    facts = self.facts.len(),
                    "ReachFactStore saturated; new reach facts are dropped and PDR will fail closed"
                );
            }
            self.saturated = true;
            return None;
        }
        let id = ReachFactId(self.facts.len());
        fact.id = id;
        self.by_pred_level
            .entry((fact.predicate, fact.level))
            .or_default()
            .push(id);
        self.facts.push(fact);
        Some(id)
    }

    pub(crate) fn try_add(&mut self, fact: ReachFact) -> Option<ReachFactId> {
        self.add_with_cap(fact, MAX_REACH_FACTS)
    }

    pub(crate) fn get(&self, id: ReachFactId) -> Option<&ReachFact> {
        self.facts.get(id.0)
    }

    pub(crate) fn len(&self) -> usize {
        self.facts.len()
    }

    pub(crate) fn ids_for_predicate_level(
        &self,
        predicate: PredicateId,
        level: usize,
    ) -> &[ReachFactId] {
        self.by_pred_level
            .get(&(predicate, level))
            .map_or(&[], Vec::as_slice)
    }

    #[cfg(test)]
    pub(crate) fn saturated(&self) -> bool {
        self.saturated
    }
}

#[allow(clippy::unwrap_used)]
#[cfg(test)]
#[path = "reach_fact_tests.rs"]
mod tests;
