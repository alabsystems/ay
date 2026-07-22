// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Derivation tracking for multi-body CHC rules.
//!
//! Integrated in Phase 3 (#1275) for multi-body rule handling.
//!
//! This mirrors Z3 Spacer's derivation concept: structured objects that track progress
//! through rules with multiple body predicates (hyperedges).
//!
//! See the development design notes for design details.

use crate::{ChcExpr, PredicateId};

use super::reach_fact::ReachFactId;

/// Unique identifier for a derivation in the store.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct DerivationId(pub(crate) usize);

/// Summary type for a premise in a derivation.
#[derive(Debug, Clone)]
pub(crate) enum PremiseSummary {
    /// Over-approximation: frame constraint projected to clause args.
    /// Used when the premise is not yet concretely reachable.
    May(ChcExpr),
    /// Concrete witness: this premise has been satisfied by a reach fact.
    /// The actual ReachFactId is stored in `Derivation::premise_rfs`.
    Must,
}

/// A single premise in a derivation (one body predicate of a CHC rule).
#[derive(Debug, Clone)]
pub(crate) struct Premise {
    /// The body predicate.
    pub(crate) predicate: PredicateId,
    /// Current summary status: may (over-approx) or must (concrete).
    pub(crate) summary: PremiseSummary,
}

/// A derivation tracks progress through a multi-body CHC rule.
///
/// When a hyperedge (rule with multiple body predicates) is satisfiable,
/// we create a derivation to track which premises need to be proven
/// concretely reachable. Only when all premises are satisfied (Must)
/// do we create the head reach fact with all premise facts as children.
#[derive(Debug, Clone)]
pub(crate) struct Derivation {
    /// Index of the clause in `ChcProblem::clauses()`.
    pub(crate) clause_index: usize,

    // Anchor: what this derivation is trying to justify as reachable.
    /// Head predicate being justified.
    pub(crate) head_predicate: PredicateId,
    /// Level at which reachability is being established.
    pub(crate) head_level: usize,
    /// State expression for the head (concrete state being justified).
    pub(crate) head_state: ChcExpr,
    /// Query clause index if this derivation originated from a query check.
    pub(crate) query_clause: Option<usize>,

    /// Premises in deterministic processing order.
    /// `Must` premises are grouped first, then `May` premises.
    pub(crate) premises: Vec<Premise>,
    /// Index of the currently active premise being processed.
    pub(crate) active: usize,

    /// Concrete premise facts collected in derivation order.
    /// Grows as premises are satisfied; complete when `len() == premises.len()`.
    pub(crate) premise_rfs: Vec<ReachFactId>,
}

impl Derivation {
    /// Returns the active premise if any remain to be processed.
    pub(crate) fn active_premise(&self) -> Option<&Premise> {
        self.premises.get(self.active)
    }

    /// Mark the current active premise as satisfied with a concrete reach fact.
    /// Advances to the next premise.
    pub(crate) fn satisfy_active(&mut self, rf: ReachFactId) {
        self.premise_rfs.push(rf);
        // Update the summary to Must if it was May
        if let Some(premise) = self.premises.get_mut(self.active) {
            premise.summary = PremiseSummary::Must;
        }
        self.active += 1;
    }

    /// Returns true if all premises have been satisfied with concrete reach facts.
    pub(crate) fn is_complete(&self) -> bool {
        self.active >= self.premises.len()
    }

    /// Returns the number of premises still needing concrete satisfaction.
    #[cfg(test)]
    pub(crate) fn remaining_premises(&self) -> usize {
        self.premises.len().saturating_sub(self.active)
    }
}

/// Storage for derivations, indexed by `DerivationId`.
///
/// Derivations are stored separately from proof obligations to avoid
/// cloning large formula data when obligations are cloned. POBs hold
/// only an optional `DerivationId` handle.
#[derive(Debug, Default)]
pub(crate) struct DerivationStore {
    /// Derivation storage (Some = active, None = freed slot).
    derivations: Vec<Option<Derivation>>,
    /// Free list for slot reuse.
    free: Vec<DerivationId>,
}

impl DerivationStore {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Allocate a new derivation and return its ID.
    pub(crate) fn alloc(&mut self, derivation: Derivation) -> DerivationId {
        if let Some(id) = self.free.pop() {
            self.derivations[id.0] = Some(derivation);
            id
        } else {
            let id = DerivationId(self.derivations.len());
            self.derivations.push(Some(derivation));
            id
        }
    }

    /// Get a reference to a derivation by ID.
    pub(crate) fn get(&self, id: DerivationId) -> Option<&Derivation> {
        self.derivations.get(id.0).and_then(|opt| opt.as_ref())
    }

    /// Get a mutable reference to a derivation by ID.
    pub(crate) fn get_mut(&mut self, id: DerivationId) -> Option<&mut Derivation> {
        self.derivations.get_mut(id.0).and_then(|opt| opt.as_mut())
    }

    /// Free a derivation slot for reuse.
    pub(crate) fn free(&mut self, id: DerivationId) {
        if let Some(slot) = self.derivations.get_mut(id.0) {
            if slot.take().is_some() {
                self.free.push(id);
            }
        }
    }
}

#[allow(clippy::unwrap_used)]
#[cfg(test)]
mod tests;
