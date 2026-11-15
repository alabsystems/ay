// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Invariant insertion facade.
//!
//! Keeps the `PdrSolver` call surface stable while moving the implementation
//! into focused sibling modules.

mod admission;
#[cfg(test)]
pub(in crate::pdr::solver) use admission::ill_typed_candidates_rejected;
mod entry_domain;
mod init_blocking;
mod predecessor_strengthening;
mod predicate_context;
mod retry;

use crate::pdr::config::InitIntBounds;
use crate::pdr::frame::Lemma;
use crate::pdr::solver::PdrSolver;
use crate::smt::SmtResult;
use crate::{ChcExpr, ChcOp, ChcSort, PredicateId};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};

impl PdrSolver {
    /// The source-name census of this problem (`fact_names::SourceNames`),
    /// or `None` when the solve is cancelled mid-census.
    ///
    /// Computed once per solver (`source_names_cache`): the problem is
    /// immutable after construction and the callers sit in per-query,
    /// per-(query, fact) and per-clause loops (`strengthen`, `init_safe`,
    /// acyclic safety, backward-chain safety, ITE blocking, the IUC frame).
    /// A census cut short by cancellation is returned as `None` and NOT cached,
    /// so `None` never outlives the cancellation it reports.
    pub(in crate::pdr::solver) fn source_names(
        &self,
    ) -> Option<std::rc::Rc<crate::pdr::solver::fact_names::SourceNames>> {
        if let Some(names) = self.source_names_cache.get() {
            return Some(std::rc::Rc::clone(names));
        }
        let mut open = || !self.is_cancelled();
        let names = std::rc::Rc::new(crate::pdr::solver::fact_names::SourceNames::collect(
            &self.problem,
            &mut open,
        )?);
        // `set` only fails if another call filled the cell meanwhile; either
        // value is the same census of the same immutable problem.
        let _ = self.source_names_cache.set(std::rc::Rc::clone(&names));
        Some(names)
    }

    /// One clause renamed apart from every other clause of the problem.
    ///
    /// Clause variables are scoped per clause, but the parser keeps the
    /// user's names: a fact, a step and a query clause routinely reuse a
    /// letter for unrelated things (VMT/lustre: the fact's init-state `I1` is
    /// the step's post-state `I1`). A query that conjoins formulas from two
    /// clauses — a fact with a step (level-1 blocking, the IUC frame, ITE
    /// blocking), a fact with a query (init-safe, acyclic safety,
    /// backward-chain safety), a fact-derived must-summary with any clause it
    /// is later applied to, a query-derived root POB with a fact at level 0 —
    /// must rename one side apart first, or the shared name equates the two
    /// variables: the query is over-constrained and its UNSAT answers can be
    /// spurious. Names are allocated by `SourceNames::rename` (fresh against
    /// every source name, `{prefix}{name}[_k]`; `query_roots` are the other
    /// formulas of the query, checked for collisions). `None` (a stopped,
    /// captured or incomplete rename) must never discharge an obligation:
    /// callers fall back to their conservative answer.
    pub(in crate::pdr::solver) fn rename_clause_apart<'a>(
        &self,
        names: &crate::pdr::solver::fact_names::SourceNames,
        prefix: &str,
        constraint: &ChcExpr,
        args: &[ChcExpr],
        query_roots: impl IntoIterator<Item = &'a ChcExpr>,
    ) -> Option<(ChcExpr, Vec<ChcExpr>)> {
        let mut open = || !self.is_cancelled();
        names.rename(constraint, args, prefix, query_roots, &mut open)
    }

    pub(in crate::pdr::solver) fn predicate_has_facts(&self, pred: PredicateId) -> bool {
        predicate_context::predicate_has_facts(self, pred)
    }

    pub(in crate::pdr::solver) fn predicate_is_reachable(&self, pred: PredicateId) -> bool {
        predicate_context::predicate_is_reachable(self, pred)
    }

    pub(in crate::pdr::solver) fn add_discovered_invariant(
        &mut self,
        pred: PredicateId,
        formula: ChcExpr,
        level: usize,
    ) -> bool {
        admission::add_discovered_invariant(self, pred, formula, level)
    }

    pub(in crate::pdr::solver) fn add_discovered_invariant_algebraic(
        &mut self,
        pred: PredicateId,
        formula: ChcExpr,
        level: usize,
    ) -> bool {
        admission::add_discovered_invariant_algebraic(self, pred, formula, level)
    }

    pub(crate) fn add_discovered_invariant_impl(
        &mut self,
        pred: PredicateId,
        formula: ChcExpr,
        level: usize,
        algebraically_verified: bool,
    ) -> bool {
        admission::add_discovered_invariant_impl(self, pred, formula, level, algebraically_verified)
    }

    pub(in crate::pdr::solver) fn try_weaken_equality_to_inequality(
        formula: &ChcExpr,
    ) -> Option<Vec<ChcExpr>> {
        admission::try_weaken_equality_to_inequality(formula)
    }

    pub(in crate::pdr::solver) fn add_discovered_invariant_with_weakening(
        &mut self,
        pred: PredicateId,
        formula: ChcExpr,
        level: usize,
    ) -> bool {
        admission::add_discovered_invariant_with_weakening(self, pred, formula, level)
    }

    pub(in crate::pdr::solver) fn build_init_constraint_from_bounds(
        &self,
        pred: PredicateId,
        bounds: &FxHashMap<String, InitIntBounds>,
    ) -> Option<ChcExpr> {
        init_blocking::build_init_constraint_from_bounds(self, pred, bounds)
    }

    pub(in crate::pdr::solver) fn has_unrestricted_incoming_inter_predicate_transitions(
        &self,
        pred: PredicateId,
    ) -> bool {
        predicate_context::has_unrestricted_incoming_inter_predicate_transitions(self, pred)
    }

    pub(in crate::pdr::solver) fn has_any_incoming_inter_predicate_transitions(
        &self,
        pred: PredicateId,
    ) -> bool {
        predicate_context::has_any_incoming_inter_predicate_transitions(self, pred)
    }

    pub(in crate::pdr::solver) fn entry_domain_constraint(
        &self,
        pred: PredicateId,
        level: usize,
    ) -> Option<ChcExpr> {
        entry_domain::entry_domain_constraint(self, pred, level)
    }

    pub(in crate::pdr::solver) fn rename_to_canonical_vars(
        expr: &ChcExpr,
        name_map: &FxHashMap<String, String>,
    ) -> ChcExpr {
        predicate_context::rename_to_canonical_vars(expr, name_map)
    }

    pub(in crate::pdr::solver) fn blocks_initial_states(
        &mut self,
        pred: PredicateId,
        formula: &ChcExpr,
    ) -> bool {
        init_blocking::blocks_initial_states(self, pred, formula)
    }

    fn try_strengthen_predecessors_for_entry(
        &mut self,
        pred: PredicateId,
        equality: &ChcExpr,
        level: usize,
    ) -> bool {
        predecessor_strengthening::try_strengthen_predecessors_for_entry(
            self, pred, equality, level,
        )
    }

    pub(in crate::pdr::solver) fn retry_deferred_entry_invariants(&mut self) {
        retry::retry_deferred_entry_invariants(self);
    }

    pub(in crate::pdr::solver) fn retry_deferred_self_inductive_invariants(&mut self) {
        retry::retry_deferred_self_inductive_invariants(self);
    }
}
