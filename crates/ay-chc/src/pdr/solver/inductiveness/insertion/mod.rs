// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Invariant insertion facade.
//!
//! Keeps the `PdrSolver` call surface stable while moving the implementation
//! into focused sibling modules.

mod admission;
mod entry_domain;
mod init_blocking;
mod predecessor_strengthening;
mod predicate_context;
mod retry;

use crate::pdr::config::InitIntBounds;
use crate::pdr::frame::Lemma;
use crate::pdr::solver::PdrSolver;
use crate::smt::SmtResult;
use crate::{ChcExpr, ChcOp, ChcSort, ChcVar, PredicateId};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};

impl PdrSolver {
    pub(in crate::pdr::solver) fn rename_fact_variables(
        fact_constraint: &ChcExpr,
        fact_head_args: &[ChcExpr],
        prefix: &str,
    ) -> (ChcExpr, Vec<ChcExpr>) {
        predicate_context::rename_fact_variables(fact_constraint, fact_head_args, prefix)
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
