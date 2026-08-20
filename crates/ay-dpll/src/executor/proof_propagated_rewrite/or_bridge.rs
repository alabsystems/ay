// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Disjunction and equivalence bridges for propagated-value replay.

use super::*;

impl PropagationChainPlanner<'_> {
    /// `(cl (not eq)) (not a) b` tautology + two resolutions:
    /// from `(cl eq)` and `(cl a)` derive `(cl b)`. `eq_term` must be an
    /// equality with argument set `{a, b}` in either stored orientation.
    pub(super) fn plan_equiv_bridge(
        &mut self,
        cx: &mut PlanCx<'_>,
        a: TermId,
        a_id: ProofId,
        b: TermId,
        eq_term: TermId,
        eq_id: ProofId,
    ) -> ProofId {
        let not_eq = self.terms.mk_not_raw(eq_term);
        let not_a = self.terms.mk_not_raw(a);
        // equiv_pos2 on (= a b): (cl (not (= a b)) (not a) b)
        // equiv_pos1 on (= b a): (cl (not (= b a)) b (not a))
        let stored_first = match self.terms.get(eq_term) {
            TermData::App(_, args) if args.len() == 2 => args[0],
            _ => a,
        };
        let (rule, clause) = if stored_first == a {
            (AletheRule::EquivPos2, vec![not_eq, not_a, b])
        } else {
            (AletheRule::EquivPos1, vec![not_eq, b, not_a])
        };
        let ep_id = cx.chain.add_rule_step(rule, clause, Vec::new(), Vec::new());
        let after_eq = cx.chain.add_rule_step(
            AletheRule::ThResolution,
            vec![not_a, b],
            vec![ep_id, eq_id],
            Vec::new(),
        );
        cx.chain.add_rule_step(
            AletheRule::ThResolution,
            vec![b],
            vec![after_eq, a_id],
            Vec::new(),
        )
    }

    /// Shape A: `before = (or d1 .. dk)` with all-distinct disjuncts; every
    /// changed disjunct must replay to literal `false`. `after` is then one
    /// of three shapes, and anything else declines:
    ///
    ///  * literal `false` — every disjunct is eliminated, the last one
    ///    through the equivalence bridge so the conclusion is exactly
    ///    `(cl false)`;
    ///  * the single surviving disjunct — the clause IS the conclusion;
    ///  * `(or survivors…)` — the disjunction is RE-FORMED (#4751). Top-level
    ///    unit propagation stores `mk_or(kept)`, which sorts and
    ///    deduplicates, so the survivor SET (not its order) must match, and
    ///    the surviving clause is folded back into the disjunction by one
    ///    `or_neg` tautology per survivor plus a resolution.
    pub(super) fn plan_or_elimination_bridge(
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
        if name != "or" || args.len() < 2 {
            return None;
        }
        let disjuncts = args.clone();
        // Slice 1 keeps the clause algebra exact: all-distinct disjuncts only.
        let distinct: HashSet<TermId> = disjuncts.iter().copied().collect();
        if distinct.len() != disjuncts.len() {
            return None;
        }
        cx.spend(disjuncts.len())?;
        let false_term = self.terms.false_term();
        let mut eliminated: Vec<(TermId, TermId, ProofId)> = Vec::new();
        let mut survivors: Vec<TermId> = Vec::new();
        for &dj in &disjuncts {
            match self.plan_derive_eq(cx, dj, stamp)? {
                EqRes::Unchanged => survivors.push(dj),
                EqRes::Changed { to, eq_term, id } => {
                    if to != false_term {
                        return None;
                    }
                    eliminated.push((dj, eq_term, id));
                }
            }
        }
        if eliminated.is_empty() {
            return None;
        }
        let clausified = cx.chain.add_rule_step(
            AletheRule::Or,
            disjuncts.clone(),
            vec![before_id],
            Vec::new(),
        );
        if after == false_term {
            if !survivors.is_empty() {
                return None;
            }
            // Resolve away all but the last disjunct, then bridge the last
            // one to (cl false) through its equivalence.
            let (last, last_eq_term, last_eq_id) = eliminated.pop()?;
            let mut clause: Vec<TermId> = disjuncts.clone();
            let mut current = clausified;
            for (dj, eq_term, eq_id) in eliminated {
                let not_dj_id = self.plan_not_disjunct(cx, dj, eq_term, eq_id);
                clause.retain(|&lit| lit != dj);
                current = cx
                    .chain
                    .add_resolution(clause.clone(), dj, current, not_dj_id);
            }
            debug_assert_eq!(clause, vec![last]);
            return Some(self.plan_equiv_bridge(
                cx,
                last,
                current,
                false_term,
                last_eq_term,
                last_eq_id,
            ));
        }
        if survivors.is_empty() {
            return None;
        }
        // Either the disjunction COLLAPSED to its single survivor (`after` is
        // that literal) or it was RE-FORMED as `(or survivors…)` (#4751 —
        // top-level unit propagation stores `mk_or(kept)`, which sorts and
        // deduplicates, so the survivor SET, not its order, is what must
        // match). Anything else declines.
        let reformed = if survivors.len() == 1 && survivors[0] == after {
            None
        } else {
            let TermData::App(Symbol::Named(head), after_args) = self.terms.get(after) else {
                return None;
            };
            if head != "or" {
                return None;
            }
            let after_args = after_args.clone();
            let mut recorded = after_args.clone();
            recorded.sort_unstable();
            let mut replayed = survivors.clone();
            replayed.sort_unstable();
            if recorded != replayed {
                return None;
            }
            cx.spend(after_args.len().checked_mul(2)?)?;
            Some(after_args)
        };
        let mut clause: Vec<TermId> = disjuncts.clone();
        let mut current = clausified;
        for (dj, eq_term, eq_id) in eliminated {
            let not_dj_id = self.plan_not_disjunct(cx, dj, eq_term, eq_id);
            clause.retain(|&lit| lit != dj);
            current = cx
                .chain
                .add_resolution(clause.clone(), dj, current, not_dj_id);
        }
        let Some(after_args) = reformed else {
            debug_assert_eq!(clause, vec![after]);
            return Some(current);
        };
        // `(cl s1 … sm)` -> `(cl (or s1 … sm))`: one `or_neg` tautology
        // `(cl after (not si))` per survivor, resolved in turn. Every step is
        // re-derived by the untouched strict checker.
        for survivor in after_args {
            let not_survivor = self.terms.mk_not_raw(survivor);
            let or_neg = cx.chain.add_rule_step(
                AletheRule::OrNeg,
                vec![after, not_survivor],
                Vec::new(),
                Vec::new(),
            );
            clause.retain(|&lit| lit != survivor);
            if !clause.contains(&after) {
                clause.push(after);
            }
            current = cx
                .chain
                .add_resolution(clause.clone(), survivor, current, or_neg);
        }
        if clause != vec![after] {
            return None;
        }
        Some(current)
    }

    /// `(cl (not dj))` from `(cl eq)` with `eq` between `dj` and literal
    /// `false`: equivalence elimination plus the `(cl (not false))`
    /// tautology.
    pub(super) fn plan_not_disjunct(
        &mut self,
        cx: &mut PlanCx<'_>,
        dj: TermId,
        eq_term: TermId,
        eq_id: ProofId,
    ) -> ProofId {
        let false_term = self.terms.false_term();
        let not_eq = self.terms.mk_not_raw(eq_term);
        let not_dj = self.terms.mk_not_raw(dj);
        let stored_first = match self.terms.get(eq_term) {
            TermData::App(_, args) if args.len() == 2 => args[0],
            _ => dj,
        };
        let (rule, clause) = if stored_first == dj {
            (AletheRule::EquivPos2, vec![not_eq, not_dj, false_term])
        } else {
            (AletheRule::EquivPos1, vec![not_eq, false_term, not_dj])
        };
        let ep_id = cx.chain.add_rule_step(rule, clause, Vec::new(), Vec::new());
        let with_false = cx.chain.add_rule_step(
            AletheRule::ThResolution,
            vec![not_dj, false_term],
            vec![ep_id, eq_id],
            Vec::new(),
        );
        let false_taut = self.plan_false_taut(cx);
        cx.chain.add_rule_step(
            AletheRule::ThResolution,
            vec![not_dj],
            vec![with_false, false_taut],
            Vec::new(),
        )
    }
}
