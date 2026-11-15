// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Derive a rewritten sole OR survivor after discharging every alternative.

use super::*;

const MAX_CHANGED_SURVIVOR_ARGS: usize = 64;

impl PropagationChainPlanner<'_> {
    /// Unlike the legacy deletion-only bridge, the remaining disjunct may
    /// itself change. First derive its ORIGINAL spelling, then bridge its
    /// independently replayed equality to the exact recorded target.
    /// The caller rolls back all failed suffixes without refunding work.
    pub(super) fn plan_changed_or_survivor(
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
        if name != "or"
            || !(2..=MAX_CHANGED_SURVIVOR_ARGS).contains(&args.len())
            || self.terms.sort(before) != &Sort::Bool
            || self.terms.sort(after) != &Sort::Bool
        {
            return None;
        }
        // Charge fanout and bounded proof emission before either allocation.
        cx.spend(args.len().checked_mul(8)?.checked_add(4)?)?;
        let disjuncts = args.clone();
        let distinct: HashSet<_> = disjuncts.iter().copied().collect();
        if distinct.len() != disjuncts.len() {
            return None;
        }
        let false_term = self.terms.false_term();
        if after == false_term {
            return None;
        }
        let mut eliminated = Vec::new();
        let mut survivor = None;
        for &disjunct in &disjuncts {
            if self.terms.sort(disjunct) != &Sort::Bool {
                return None;
            }
            match self.plan_derive_eq(cx, disjunct, stamp)? {
                EqRes::Unchanged if disjunct == false_term => {
                    eliminated.push((disjunct, None));
                }
                EqRes::Changed { to, eq_term, id } if to == false_term => {
                    eliminated.push((disjunct, Some((eq_term, id))));
                }
                EqRes::Changed { to, eq_term, id } if to == after && survivor.is_none() => {
                    survivor = Some((disjunct, eq_term, id));
                }
                _ => return None,
            }
        }
        let (original_survivor, equality, equality_id) = survivor?;
        if eliminated.is_empty() {
            return None;
        }
        let mut clause = disjuncts;
        let mut current =
            cx.chain
                .add_rule_step(AletheRule::Or, clause.clone(), vec![before_id], Vec::new());
        for (disjunct, equality) in eliminated {
            let negated = match equality {
                Some((eq_term, eq_id)) => self.plan_not_disjunct(cx, disjunct, eq_term, eq_id),
                None => self.plan_false_taut(cx),
            };
            clause.retain(|&term| term != disjunct);
            current = cx
                .chain
                .add_resolution(clause.clone(), disjunct, current, negated);
        }
        if clause != vec![original_survivor] {
            return None;
        }
        Some(self.plan_equiv_bridge(cx, original_survivor, current, after, equality, equality_id))
    }
}

#[cfg(test)]
mod tests;
