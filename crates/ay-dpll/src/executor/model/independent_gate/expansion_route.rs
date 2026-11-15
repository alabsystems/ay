// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The quantified model gate's EXPANSION route (#qlra-nested-cegqi, plan
//! §4.2): confirm-only, consulted after every other route left a conjunct
//! undecided.
//!
//! It rebuilds, itself, the quantifier-free Herbrand expansion `E` of the
//! negated SOURCE conjunct (`crate::executor::expansion::qf_formula`):
//! universals of `¬R` at the instance tuples a producer installed as hints,
//! existentials of `¬R` Skolemized with fresh gate constants. It then pins
//! the conjunct's free constants to the emitted model's values
//! (`quantified_gate_model_pins`, the gate Skolems excluded) and asks the
//! checked disposable ground solve for `pins ∧ E`. Only a checked UNSAT whose
//! token is consumed against its exact roots confirms: `pins ∧ E` UNSAT ⇒
//! `pins ∧ ¬R` UNSAT ⇒ the model satisfies `R` (even under partial pins).
//! Anything else — no current hints, a declined expansion, SAT, unknown, a
//! stale token — returns `None` and the gate's existing outcome stands.
//!
//! The hints are untrusted DATA: every tuple is a sound instance, so a forged
//! hint can only fail to confirm. The route mints no grant and no handoff; a
//! confirmation is an ordinary `QuantifiedModelCheck::Confirmed` that the
//! gate's sealed check scope still binds to this exact model and query.

use super::{
    independent_gate_query_roots, CheckedGroundDecision, Executor, HashSet,
    QuantifiedGateCheckedGroundDecision, QuantifiedGateElements, QuantifiedModelCheck, TermId,
};
use crate::executor::expansion::qf_formula::negated_expansion;

#[cfg(test)]
#[path = "expansion_route_tests.rs"]
mod tests;

impl Executor {
    /// The installed expansion hints' tuples, when they are bound to the
    /// current query epoch, its exact roots and a live store prefix.
    fn quantified_gate_current_expansion_hints(
        &self,
    ) -> Option<crate::executor::expansion::InstanceHints> {
        let hints = self.qlra_lane.expansion_hints.as_deref()?;
        let current = hints.epoch.is_same_epoch(&self.query_authority_epoch)
            && hints.stamp.is_append_only_prefix_of(&self.ctx.terms)
            && hints.roots == independent_gate_query_roots(self).ok()?;
        current.then(|| hints.tuples.clone())
    }

    /// Confirm `source` (an authored quantified conjunct) through a checked
    /// refutation of its negated expansion, or `None`.
    pub(super) fn quantified_gate_expansion_check(
        &mut self,
        source: TermId,
    ) -> Option<QuantifiedModelCheck> {
        let tuples = self.quantified_gate_current_expansion_hints()?;
        if let Some(hints) = self.qlra_lane.expansion_hints.as_deref() {
            hints.consulted.set(hints.consulted.get().saturating_add(1));
        }
        if self.solve_deadline.expired() {
            return None;
        }
        let expansion = negated_expansion(&mut self.ctx.terms, source, &tuples).ok()?;
        let mut elems = QuantifiedGateElements::default();
        let exclude: HashSet<TermId> = expansion.skolems.iter().copied().collect();
        let pins = self.quantified_gate_model_pins(expansion.formula, &mut elems, &exclude);
        let mut nested = pins.equalities;
        nested.extend(elems.distinct_assertions(&mut self.ctx.terms));
        nested.push(expansion.formula);
        let decision = self.quantified_gate_checked_confirming_solve(nested);
        tracing::debug!(
            target: "ay::qlra",
            "gate expansion route: instances={} skolems={} decision={decision:?}",
            expansion.instances,
            expansion.skolems.len()
        );
        let Some(QuantifiedGateCheckedGroundDecision {
            decision: CheckedGroundDecision::Unsat(proof),
            roots,
        }) = decision
        else {
            return None;
        };
        if !proof.consume(self, &roots) {
            return None;
        }
        if let Some(hints) = self.qlra_lane.expansion_hints.as_deref() {
            hints.confirmed.set(hints.confirmed.get().saturating_add(1));
        }
        Some(QuantifiedModelCheck::Confirmed)
    }
}
