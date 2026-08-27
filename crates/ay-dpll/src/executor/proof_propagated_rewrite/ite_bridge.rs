// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `ite` replay for the propagated-rewrite planner (#4751).

use super::*;

impl PropagationChainPlanner<'_> {
    /// Replay a rewritten `ite`, or report it unchanged.
    pub(super) fn plan_ite_arm(
        &mut self,
        cx: &mut PlanCx<'_>,
        t: TermId,
        stamp: u32,
        children: [TermId; 3],
    ) -> Option<EqRes> {
        let mut results = Vec::with_capacity(children.len());
        let mut any_changed = false;
        for &child in &children {
            let result = self.plan_derive_eq(cx, child, stamp)?;
            any_changed |= matches!(result, EqRes::Changed { .. });
            results.push(result);
        }
        if !any_changed {
            return Some(EqRes::Unchanged);
        }
        // SCOPED to the `EqDiffVar` lane, for the reason `connective_reorder`
        // records: a rewritten `ite` child declined outright before, and
        // deriving it for the `PropagateValues` replay too changes which UNSATs
        // that lane certifies. Measured on the ay-chc `array_ghost_pair` route
        // fixture.
        cx.eqdv_by_atom.as_ref()?;
        self.plan_ite_congruence(cx, t, &children, &results)
    }

    /// Ternary congruence for a rewritten `ite` (#4751).
    ///
    /// Before this arm a changed `ite` child failed the plan outright, so a
    /// whole assertion declined the moment one of its `ite` BRANCHES was
    /// rewritten — the shape `dillig12_m`'s transition relation is built from
    /// (`(ite (= 1 v8) (= a b) (= c e))`). `ite` is a dedicated `TermData` node
    /// rather than an `App`, but `validate_cong` already treats it as an
    /// ordinary ternary function and discharges each argument pair with a
    /// premise equality, so this adds no rule.
    ///
    /// Fail-closed exactly like the `not` arm: `mk_ite` may FOLD (a constant
    /// condition, or two branches that became the same node), and a fold makes
    /// the congruence conclusion name a node the premises do not build. The
    /// rebuild is therefore re-read and anything but the structural
    /// three-child `ite` declines, which is what the arm did unconditionally
    /// before.
    fn plan_ite_congruence(
        &mut self,
        cx: &mut PlanCx<'_>,
        term: TermId,
        children: &[TermId; 3],
        results: &[EqRes],
    ) -> Option<EqRes> {
        cx.spend(2)?;
        let new_children: Vec<TermId> = children
            .iter()
            .zip(results)
            .map(|(&child, result)| match result {
                EqRes::Unchanged => child,
                EqRes::Changed { to, .. } => *to,
            })
            .collect();
        let rebuilt = self
            .terms
            .mk_ite(new_children[0], new_children[1], new_children[2]);
        if rebuilt == term || cx.refuses_constant_conclusion(rebuilt) {
            return None;
        }
        match self.terms.get(rebuilt) {
            TermData::Ite(condition, then_branch, else_branch)
                if [*condition, *then_branch, *else_branch] == new_children[..] => {}
            _ => return None,
        }
        let premises = Self::congruence_premises(children, results, &new_children)?;
        let eq_term = self
            .terms
            .mk_app(Symbol::named("="), [term, rebuilt], Sort::Bool);
        match self.terms.get(eq_term) {
            TermData::App(symbol, args)
                if symbol.name() == "=" && args.as_slice() == [term, rebuilt] => {}
            _ => return None,
        }
        let id = cx
            .chain
            .add_rule_step(AletheRule::Cong, vec![eq_term], premises, Vec::new());
        Some(EqRes::Changed {
            to: rebuilt,
            eq_term,
            id,
        })
    }
}
