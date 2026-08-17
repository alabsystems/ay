// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! And-headed conjunct-elimination bridge for propagated-value replay
//! (#ppp-l3).
//!
//! `PropagateValues` can fold a conjunct of a nested `(and c1 .. ck)` to
//! literal `true`; the canonical `mk_and` rebuild then DROPS the vanished
//! conjunct (also flattening nested `and`s and deduplicating), so the
//! recorded rewrite is `(and c1 .. ck) -> (and s1 .. sm)` or a single
//! surviving conjunct. The equality replay cannot bridge that shape (the
//! rebuilt argument list changes arity), but at the CLAUSE level the
//! derivation is exact with existing rules only:
//!
//!  * every survivor `si` is reachable from `(cl before)` through the
//!    existing nested `and_pos`/resolution chains;
//!  * `and_neg` on the surviving conjunction plus one resolution per
//!    survivor concludes `(cl after)`.
//!
//! The record stays a HINT: each changed conjunct is independently replayed
//! to literal `true` and the canonical `fold_rebuild` must reproduce the
//! recorded `after` exactly, or the plan DECLINES (fail-closed, the assume
//! falls back to today's demotion path). No checker rule is added or
//! widened.

use super::clause::AndPath;
use super::*;

impl PropagationChainPlanner<'_> {
    /// Shape B (#ppp-l3): `before = (and c1 .. ck)`; every changed conjunct
    /// must replay to literal `true` and the canonical rebuild must equal
    /// `after`. Derives `(cl after)` from `(cl before)`.
    pub(super) fn plan_and_elimination_bridge(
        &mut self,
        cx: &mut PlanCx<'_>,
        before: TermId,
        before_id: ProofId,
        after: TermId,
        stamp: u32,
    ) -> Option<ProofId> {
        let TermData::App(Symbol::Named(name), args) = self.terms.get(before) else {
            return None;
        };
        if name != "and" || args.len() < 2 {
            return None;
        }
        let conjuncts = args.clone();
        cx.spend(conjuncts.len())?;
        let true_term = self.terms.true_term();
        // An assume of literal `true` carries no refutation content; out of
        // scope for the bridge.
        if after == true_term || after == before {
            return None;
        }
        // Replay verification: mirror the pass on every conjunct. Changed
        // conjuncts must fold to literal `true` (the eliminated shape this
        // bridge certifies); anything else declines.
        let mut new_args = Vec::with_capacity(conjuncts.len());
        let mut any_changed = false;
        for &conjunct in &conjuncts {
            match self.plan_derive_eq(cx, conjunct, stamp)? {
                EqRes::Unchanged => new_args.push(conjunct),
                EqRes::Changed { to, .. } => {
                    if to != true_term {
                        return None;
                    }
                    any_changed = true;
                    new_args.push(to);
                }
            }
        }
        if !any_changed {
            return None;
        }
        let folded =
            PropagateValues::fold_rebuild(self.terms, Symbol::named("and"), before, new_args);
        if folded != after {
            return None;
        }
        match self.terms.get(after).clone() {
            TermData::App(Symbol::Named(head), folded_args) if head == "and" => {
                self.plan_surviving_conjunction(cx, before, before_id, after, &folded_args)
            }
            _ => {
                // Single-survivor collapse: `after` must sit on a (possibly
                // nested) and-path of `before`.
                let AndPath::Found(path) = Self::plan_find_and_path(self.terms, cx, before, after)?
                else {
                    return None;
                };
                if path.is_empty() {
                    return None;
                }
                Some(self.plan_emit_and_pos_chain_from(cx, before_id, before, &path))
            }
        }
    }

    /// `(cl (and s1 .. sm))` from `(cl before)`: derive each survivor via an
    /// and-path chain, then discharge `and_neg`'s negated conjuncts.
    fn plan_surviving_conjunction(
        &mut self,
        cx: &mut PlanCx<'_>,
        before: TermId,
        before_id: ProofId,
        after: TermId,
        folded_args: &[TermId],
    ) -> Option<ProofId> {
        cx.spend(folded_args.len().checked_mul(2)?)?;
        let mut survivor_ids = Vec::with_capacity(folded_args.len());
        for &survivor in folded_args {
            let AndPath::Found(path) = Self::plan_find_and_path(self.terms, cx, before, survivor)?
            else {
                return None;
            };
            survivor_ids.push(self.plan_emit_and_pos_chain_from(cx, before_id, before, &path));
        }
        let negated: Vec<TermId> = folded_args
            .iter()
            .map(|&survivor| self.terms.mk_not_raw(survivor))
            .collect();
        let mut clause = Vec::with_capacity(folded_args.len() + 1);
        clause.push(after);
        clause.extend(negated.iter().copied());
        let mut current =
            cx.chain
                .add_rule_step(AletheRule::AndNeg, clause.clone(), Vec::new(), vec![after]);
        for ((&survivor, survivor_id), not_survivor) in
            folded_args.iter().zip(survivor_ids).zip(negated)
        {
            clause.retain(|&literal| literal != not_survivor);
            current = cx
                .chain
                .add_resolution(clause.clone(), survivor, current, survivor_id);
        }
        if clause != vec![after] {
            return None;
        }
        Some(current)
    }
}
