// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Relational invariant discovery for PDR solver.
//!
//! Discovers invariants of the form `var_i <= var_j` or `var_i >= var_j`
//! that hold initially and are preserved by all transitions.
//!
//! ## Algorithm
//!
//! **Phase 1**: For predicates with fact clauses (initial states):
//! - Check if a relational ordering holds in the initial state
//! - Verify the ordering is preserved by all transitions
//!
//! **Phase 2**: For predicates without fact clauses:
//! - Infer orderings from incoming cross-predicate transitions
//! - Verify preservation by self-loop transitions
//! - Iterate until fixpoint
//!
//! ## Example
//!
//! For a loop `while (i < n) { i += 2; }`, discovers `i <= n`.
//!
//! ## Key Methods
//!
//! - [`PdrSolver::discover_relational_invariants`] - Main discovery entry point

use super::super::PdrSolver;
use crate::{ChcExpr, ChcSort};

impl PdrSolver {
    /// Discover relational invariants proactively.
    ///
    /// Discovers invariants of the form `var_i <= var_j` or `var_i >= var_j`
    /// that hold initially and are preserved by all transitions.
    ///
    /// These are useful for bounding loop counters.
    pub(in crate::pdr::solver) fn discover_relational_invariants(&mut self) {
        let predicates: Vec<_> = self.problem.predicates().to_vec();

        if self.config.verbose {
            safe_eprintln!(
                "PDR: discover_relational_invariants: {} predicates, facts: {:?}",
                predicates.len(),
                self.caches.predicates_with_facts
            );
        }

        for pred in &predicates {
            if !self.predicate_has_facts(pred.id) {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: discover_relational_invariants: skipping pred {} (no facts)",
                        pred.id.index()
                    );
                }
                continue;
            }

            let canonical_vars = match self.canonical_vars(pred.id) {
                Some(v) => v.to_vec(),
                None => continue,
            };

            if canonical_vars.len() < 2 || canonical_vars.len() > super::MAX_PAIRWISE_DISCOVERY_VARS
            {
                continue;
            }

            let init_values = self.get_init_values(pred.id);
            // #7048: Skip relational invariants involving constant variables.
            let mut constant_args = self.detect_constant_arguments(pred.id);
            constant_args.extend(self.detect_frame_tight_bound_vars(pred.id).iter());

            for i in 0..canonical_vars.len() {
                // Check cancellation to support solve_timeout / portfolio solving
                if self.is_cancelled() {
                    return;
                }
                for j in 0..canonical_vars.len() {
                    if i == j {
                        continue;
                    }
                    // #7048: Skip pairs involving constant variables — their ordering
                    // is fully determined by tight bounds.
                    if constant_args.contains(&i) || constant_args.contains(&j) {
                        continue;
                    }

                    let var_i = &canonical_vars[i];
                    let var_j = &canonical_vars[j];

                    if !matches!(var_i.sort, ChcSort::Int) || !matches!(var_j.sort, ChcSort::Int) {
                        continue;
                    }

                    let init_i = init_values.get(&var_i.name);
                    let init_j = init_values.get(&var_j.name);

                    let init_holds_le = match (init_i, init_j) {
                        (Some(bi), Some(bj)) if bi.max <= bj.min => true,
                        _ => {
                            let violates_le = ChcExpr::gt(
                                ChcExpr::var(var_i.clone()),
                                ChcExpr::var(var_j.clone()),
                            );
                            self.blocks_initial_states(pred.id, &violates_le)
                        }
                    };

                    if init_holds_le && self.is_le_preserved_by_transitions(pred.id, var_i, var_j) {
                        let le_invariant =
                            ChcExpr::le(ChcExpr::var(var_i.clone()), ChcExpr::var(var_j.clone()));
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: Discovered relational invariant for pred {}: {} <= {}",
                                pred.id.index(),
                                var_i.name,
                                var_j.name
                            );
                        }
                        self.add_discovered_invariant(pred.id, le_invariant, 1);
                    }

                    let init_holds_ge = match (init_i, init_j) {
                        (Some(bi), Some(bj)) if bi.min >= bj.max => true,
                        _ => {
                            let violates_ge = ChcExpr::lt(
                                ChcExpr::var(var_i.clone()),
                                ChcExpr::var(var_j.clone()),
                            );
                            self.blocks_initial_states(pred.id, &violates_ge)
                        }
                    };

                    if init_holds_ge && self.is_ge_preserved_by_transitions(pred.id, var_i, var_j) {
                        let ge_invariant =
                            ChcExpr::ge(ChcExpr::var(var_i.clone()), ChcExpr::var(var_j.clone()));
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: Discovered relational invariant for pred {}: {} >= {}",
                                pred.id.index(),
                                var_i.name,
                                var_j.name
                            );
                        }
                        self.add_discovered_invariant(pred.id, ge_invariant, 1);
                    }
                }
            }
        }

        // Phase 2: Propagate orderings to predicates without fact clauses.
        // Iterate until fixpoint: for each such predicate, check if incoming
        // cross-predicate transitions enforce an ordering, and if so, verify
        // it's preserved by self-loops.
        let mut propagated = true;
        while propagated {
            propagated = false;
            for pred in &predicates {
                if self.predicate_has_facts(pred.id) {
                    continue;
                }
                let canonical_vars = match self.canonical_vars(pred.id) {
                    Some(v) => v.to_vec(),
                    None => continue,
                };
                if canonical_vars.len() < 2
                    || canonical_vars.len() > super::MAX_PAIRWISE_DISCOVERY_VARS
                {
                    continue;
                }
                for i in 0..canonical_vars.len() {
                    for j in 0..canonical_vars.len() {
                        if i == j {
                            continue;
                        }
                        let var_i = &canonical_vars[i];
                        let var_j = &canonical_vars[j];
                        if !matches!(var_i.sort, ChcSort::Int)
                            || !matches!(var_j.sort, ChcSort::Int)
                        {
                            continue;
                        }
                        let le_invariant =
                            ChcExpr::le(ChcExpr::var(var_i.clone()), ChcExpr::var(var_j.clone()));
                        let le_already_known = self.frames.len() > 1
                            && self.frames[1]
                                .lemmas
                                .iter()
                                .any(|l| l.predicate == pred.id && l.formula == le_invariant);
                        if !le_already_known
                            && self.is_le_enforced_by_incoming_transitions(pred.id, i, j)
                            && self.is_le_preserved_by_transitions(pred.id, var_i, var_j)
                            && self.add_discovered_invariant(pred.id, le_invariant, 1)
                        {
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: Propagated relational invariant for pred {}: {} <= {}",
                                    pred.id.index(),
                                    var_i.name,
                                    var_j.name
                                );
                            }
                            propagated = true;
                        }
                        let ge_invariant =
                            ChcExpr::ge(ChcExpr::var(var_i.clone()), ChcExpr::var(var_j.clone()));
                        let ge_already_known = self.frames.len() > 1
                            && self.frames[1]
                                .lemmas
                                .iter()
                                .any(|l| l.predicate == pred.id && l.formula == ge_invariant);
                        if !ge_already_known
                            && self.is_ge_enforced_by_incoming_transitions(pred.id, i, j)
                            && self.is_ge_preserved_by_transitions(pred.id, var_i, var_j)
                            && self.add_discovered_invariant(pred.id, ge_invariant, 1)
                        {
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: Propagated relational invariant for pred {}: {} >= {}",
                                    pred.id.index(),
                                    var_i.name,
                                    var_j.name
                                );
                            }
                            propagated = true;
                        }
                    }
                }
            }
        }
    }
}

#[allow(clippy::unwrap_used)]
#[cfg(test)]
#[path = "relational_tests.rs"]
mod tests;
