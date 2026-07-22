// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SCC (strongly connected component) strengthening for multi-predicate lemmas.
//!
//! When a blocking lemma is discovered for one predicate in a cyclic SCC,
//! `try_scc_strengthening` translates it to all other SCC members and
//! verifies joint inductiveness via `verify_scc_lemmas`.

use super::{ChcExpr, FxHashMap, PdrSolver, PredicateId, SmtResult};

impl PdrSolver {
    /// Try to strengthen all predicates in the same SCC using a trigger invariant.
    ///
    /// When a blocking lemma is learned for `trigger_pred`, this method translates
    /// it to all other predicates in the same SCC and verifies joint inductiveness.
    ///
    /// Input: `trigger_invariant` is the invariant from `BlockResult::Blocked(lemma).formula`
    /// Output: Vector of (predicate, invariant) pairs for all SCC members
    pub(in crate::pdr::solver) fn try_scc_strengthening(
        &mut self,
        trigger_pred: PredicateId,
        trigger_invariant: &ChcExpr,
        level: usize,
    ) -> Option<Vec<(PredicateId, ChcExpr)>> {
        let scc_idx = *self.scc_info.predicate_to_scc.get(&trigger_pred)?;
        let scc = &self.scc_info.sccs[scc_idx];

        if !scc.is_cyclic || scc.predicates.len() <= 1 {
            return None; // Not a multi-predicate cycle
        }

        if self.config.verbose {
            safe_eprintln!(
                "PDR: Attempting SCC strengthening for pred {} at level {} with lemma: {}",
                trigger_pred.index(),
                level,
                trigger_invariant
            );
        }

        // Build conjectured invariants for all SCC members
        let mut invariants: FxHashMap<PredicateId, ChcExpr> = FxHashMap::default();
        for pred in &scc.predicates {
            if let Some(translated) = self.translate_lemma(trigger_invariant, trigger_pred, *pred) {
                invariants.insert(*pred, translated);
            } else {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: SCC strengthening failed: cannot translate lemma from pred {} to pred {}",
                        trigger_pred.index(),
                        pred.index()
                    );
                }
                return None;
            }
        }

        // Verify joint inductiveness
        // Clone the SCC predicates to avoid borrow issues
        let scc_predicates: Vec<PredicateId> = scc.predicates.clone();
        if !self.verify_scc_lemmas(&scc_predicates, &invariants, level) {
            if self.config.verbose {
                safe_eprintln!("PDR: SCC strengthening failed: lemmas not jointly inductive");
            }
            return None;
        }

        // Success - return invariants for all SCC predicates
        Some(invariants.into_iter().collect())
    }

    /// Verify that conjectured lemmas are jointly inductive for an SCC.
    ///
    /// `invariants` maps each SCC predicate to its invariant (Lemma.formula).
    ///
    /// For inductiveness, we check that for each transition clause:
    /// `frame[level-1] AND T AND body_invariants AND NOT(head_invariant)` is UNSAT
    ///
    /// The key difference from standard PDR:
    /// - Standard: body constraints come only from cumulative_frame_constraint
    /// - SCC: body constraints ALSO include the conjectured invariants
    ///
    /// This breaks the cyclic dependency: all SCC predicates assume the others
    /// have the conjectured invariants, and we verify this assumption holds.
    pub(in crate::pdr::solver) fn verify_scc_lemmas(
        &mut self,
        scc_predicates: &[PredicateId],
        invariants: &FxHashMap<PredicateId, ChcExpr>,
        level: usize,
    ) -> bool {
        // First, check init validity: invariants must hold at all init states
        for pred in scc_predicates {
            if let Some(invariant) = invariants.get(pred) {
                // Check if this predicate has fact clauses (init states)
                if self.predicate_has_facts(*pred) {
                    // Init constraint => invariant must hold
                    // Equivalently: init_constraint AND NOT(invariant) must be UNSAT
                    let blocking = ChcExpr::not(invariant.clone());
                    if !self.blocks_initial_states(*pred, &blocking) {
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: SCC verify_scc_lemmas: invariant for pred {} does not hold at all init states: {}",
                                pred.index(), invariant
                            );
                        }
                        return false;
                    }
                }
            }
        }

        // Then check transition inductiveness: for each transition clause,
        // frame ∧ T ∧ NOT(head_invariant) must be UNSAT
        for pred in scc_predicates {
            for clause in self.problem.clauses_defining(*pred).cloned() {
                // Skip fact clauses (init) - we checked them above
                if clause.body.predicates.is_empty() {
                    continue;
                }

                // Get head predicate and its invariant
                let head_pred = match clause.head.predicate_id() {
                    Some(p) => p,
                    None => continue, // Query clause
                };
                let head_invariant = match invariants.get(&head_pred) {
                    Some(inv) => inv.clone(),
                    None => continue, // Not in SCC
                };

                // Build conjunction: constraint AND body_frames AND body_scc_invariants AND NOT(head_invariant)
                let mut conjuncts = vec![clause
                    .body
                    .constraint
                    .clone()
                    .unwrap_or(ChcExpr::Bool(true))];

                // Add frame constraints and conjectured invariants for body predicates
                for (body_pred, body_args) in &clause.body.predicates {
                    // Use frame constraints from all levels up to and including the
                    // current level. Previously this used level-1, which excluded lemmas
                    // already accepted at the current level. This caused individual SCC
                    // lemma checks to fail because they couldn't see sibling lemmas that
                    // were added to the same frame earlier in the discovery loop.
                    // (#2472: dillig03_m regression — inv.a0>=1 accepted but invisible
                    // when checking inv.a1>=1 across the inv→itp→inv cycle.)
                    if let Some(frame) = self.cumulative_frame_constraint(level, *body_pred) {
                        if let Some(applied) = self.apply_to_args(*body_pred, &frame, body_args) {
                            conjuncts.push(applied);
                        }
                    }
                    // Add conjectured SCC invariant (this is the key difference!)
                    if let Some(body_invariant) = invariants.get(body_pred) {
                        if let Some(applied) =
                            self.apply_to_args(*body_pred, body_invariant, body_args)
                        {
                            conjuncts.push(applied);
                        }
                    }
                }

                // Add negated head invariant (we're checking if we can reach states violating it)
                let head_args = match &clause.head {
                    crate::ClauseHead::Predicate(_, args) => args.as_slice(),
                    crate::ClauseHead::False => continue,
                };
                let neg_head_invariant = ChcExpr::not(head_invariant);
                if let Some(applied) = self.apply_to_args(head_pred, &neg_head_invariant, head_args)
                {
                    conjuncts.push(applied);
                }

                // Check: is the conjunction UNSAT?
                // If UNSAT: no transition can violate the head's invariant (good!)
                // If SAT: transition can reach state violating invariant (inductiveness fails)
                //
                // Use equality propagation + ITE case-split fallback like other
                // inductiveness checks. Plain check_sat returns Unknown on clauses
                // with ite(mod ...) expressions (e.g., dillig02_m), causing valid
                // SCC invariants to be incorrectly rejected. Part of #3121.
                let query = ChcExpr::and_all(conjuncts);
                let simplified = query.propagate_equalities();
                if matches!(simplified, ChcExpr::Bool(false)) {
                    continue;
                }
                let (smt_result, _) = Self::check_sat_with_ite_case_split(
                    &mut self.smt,
                    self.config.verbose,
                    &simplified,
                );
                match smt_result {
                    SmtResult::Unsat
                    | SmtResult::UnsatWithCore(_)
                    | SmtResult::UnsatWithFarkas(_) => continue,
                    _ => {
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: SCC inductiveness check failed for clause defining pred {}",
                                head_pred.index()
                            );
                        }
                        return false;
                    }
                }
            }
        }

        // Single-step checks are sufficient for correctness.
        //
        // A full-cycle inductiveness check was tried in #138 but its
        // SMT-query construction had bugs that caused it to reject valid
        // invariants (e.g., `pdr_s_multipl_12_safe`). The experimental
        // `check_full_cycle_inductiveness` helper was removed with #138
        // when the issue was closed; any future coverage extension should
        // start from the Z3/Golem SCC invariant machinery rather than
        // resurrecting the old implementation.
        true
    }
}
