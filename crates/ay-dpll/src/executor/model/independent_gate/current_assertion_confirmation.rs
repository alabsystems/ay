// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Current-query quantified-leaf confirmation for SAT restoration.

use super::{contains_quantifier, Executor, QuantifiedModelCheck, TermData};

impl Executor {
    /// Positively certify every quantified leaf in the CURRENT assertion set
    /// against the retained model, using the same checker as the mandatory
    /// publication gate.
    ///
    /// Quantifier-result restoration invokes this only after ordinary model
    /// validation checked the ground siblings but skipped a quantifier. The
    /// bridge admits only a provably vacuous binder or a closed, fixed-sort
    /// existential prefix; it cannot become generic post-hoc SAT authority for
    /// live model-dependent quantifiers. Every admitted leaf must return
    /// [`QuantifiedModelCheck::Confirmed`]. A refutation, deferral,
    /// indeterminate result, missing model, recursion, or exhausted deadline
    /// preserves the existing fail-closed `Unknown` path.
    pub(in crate::executor) fn quantified_model_gate_confirms_current_assertions(
        &mut self,
    ) -> bool {
        if self.last_model.is_none() || self.in_quantified_model_gate {
            return false;
        }

        let assertions = self.ctx.assertions.clone();
        let mut candidates = Vec::new();
        // Arming and the obligation set are separate. At least one leaf must
        // satisfy the narrow restoration predicate, while every quantified
        // leaf must confirm. Filtering the obligation set to only armed leaves
        // once allowed a live false sibling to escape this internal gate.
        let mut has_armed_leaf = false;
        for assertion in assertions {
            if !contains_quantifier(&self.ctx.terms, assertion) {
                continue;
            }
            let mut conjuncts = Vec::new();
            crate::executor::quantifier_loop::collect_and_conjuncts(
                &self.ctx.terms,
                assertion,
                &mut conjuncts,
            );
            if conjuncts.is_empty() {
                conjuncts.push(assertion);
            }
            for conjunct in conjuncts {
                let is_and_node = matches!(
                    self.ctx.terms.get(conjunct),
                    TermData::App(sym, _) if sym.name() == "and"
                );
                if !is_and_node && contains_quantifier(&self.ctx.terms, conjunct) {
                    has_armed_leaf |= self.quantified_gate_restoration_candidate(conjunct);
                    if !candidates.contains(&conjunct) {
                        candidates.push(conjunct);
                    }
                }
            }
        }
        if !has_armed_leaf || candidates.is_empty() {
            return false;
        }

        // This is the SECOND quantified-model-gate arm site, and it runs on the
        // same public `check-sat` as (and BEFORE) the publication gate. Both
        // therefore draw their wall from ONE query-owned envelope; a fresh
        // per-arm constant here would let a single query pay the gate's ground
        // probes twice over.
        let (arm, saved_deadline) = self.open_quantified_gate_arm();
        let saved_statistics = self.last_statistics.clone();
        self.in_quantified_model_gate = true;
        let confirmed = candidates.into_iter().all(|conjunct| {
            !self.solve_deadline.expired()
                && matches!(
                    self.check_quantified_conjunct_against_model(conjunct),
                    QuantifiedModelCheck::Confirmed
                )
        });
        self.in_quantified_model_gate = false;
        self.close_quantified_gate_arm(arm, saved_deadline);
        self.last_statistics = saved_statistics;
        confirmed
    }
}
