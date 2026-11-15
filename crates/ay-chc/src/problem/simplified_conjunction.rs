// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The guard conjunction of one OR-split (`try_split_ors_in_clauses`).

use std::sync::Arc;

use ay_core::kani_compat::DetHashSet as FxHashSet;

use crate::{ChcExpr, ChcOp};

/// A conjunction kept in the form `simplify_constants(and_all(..))` gives it:
/// each conjunct `simplify_constants`-normal and not itself an `and`, no `true`
/// or duplicate conjunct, and `false` as soon as a conjunct is `false` or a
/// conjunct and its negation are both present. [`Self::conjoin`] simplifies
/// only the extra expression and checks it against the guard's hash sets, so
/// one branch costs O(|branch|) plus a copy of the guard's conjunct list
/// instead of a re-simplification of the whole guard.
pub(super) struct SimplifiedConjunction {
    guard: Conjuncts,
}

#[derive(Default)]
struct Conjuncts {
    /// Conjuncts in first-occurrence order.
    list: Vec<Arc<ChcExpr>>,
    /// Every conjunct in `list`.
    seen: FxHashSet<Arc<ChcExpr>>,
    /// `e` for every conjunct `(not e)` in `list`.
    negated: FxHashSet<Arc<ChcExpr>>,
    /// A conjunct was `false`, or a conjunct and its negation are both present.
    refuted: bool,
}

impl Conjuncts {
    fn has(
        &self,
        base: Option<&Self>,
        set: impl Fn(&Self) -> &FxHashSet<Arc<ChcExpr>>,
        e: &Arc<ChcExpr>,
    ) -> bool {
        set(self).contains(e) || base.is_some_and(|b| set(b).contains(e))
    }

    /// Add a `simplify_constants`-normal expression, flattening `and`. A
    /// conjunct already in `base` (the guard a branch is conjoined to) is a
    /// duplicate, and one complementary to a `base` conjunct refutes.
    fn push(&mut self, simplified: ChcExpr, base: Option<&Self>) {
        let mut pending = vec![Arc::new(simplified)];
        while let Some(item) = pending.pop() {
            if self.refuted {
                return;
            }
            match item.as_ref() {
                ChcExpr::Bool(true) => {}
                ChcExpr::Bool(false) => self.refuted = true,
                ChcExpr::Op(ChcOp::And, args) => pending.extend(args.iter().rev().cloned()),
                other => {
                    if self.has(base, |c| &c.seen, &item) {
                        continue;
                    }
                    let negation_of = match other {
                        ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => Some(&args[0]),
                        _ => None,
                    };
                    if self.has(base, |c| &c.negated, &item)
                        || negation_of.is_some_and(|e| self.has(base, |c| &c.seen, e))
                    {
                        self.refuted = true;
                        return;
                    }
                    if let Some(e) = negation_of {
                        self.negated.insert(Arc::clone(e));
                    }
                    self.seen.insert(Arc::clone(&item));
                    self.list.push(item);
                }
            }
        }
    }
}

impl SimplifiedConjunction {
    pub(super) fn from_conjuncts(conjuncts: Vec<ChcExpr>) -> Self {
        let mut guard = Conjuncts::default();
        for conjunct in conjuncts {
            guard.push(conjunct.simplify_constants(), None);
        }
        Self { guard }
    }

    /// The guard conjoined with `extra`, as a clause constraint (`None` for
    /// `true`).
    pub(super) fn conjoin(&self, extra: ChcExpr) -> Option<ChcExpr> {
        if self.guard.refuted {
            return Some(ChcExpr::Bool(false));
        }
        let mut branch = Conjuncts::default();
        branch.push(extra.simplify_constants(), Some(&self.guard));
        if branch.refuted {
            return Some(ChcExpr::Bool(false));
        }
        let mut all = Vec::with_capacity(self.guard.list.len() + branch.list.len());
        all.extend(self.guard.list.iter().cloned());
        all.extend(branch.list);
        match all.len() {
            0 => None,
            1 => Some(all[0].as_ref().clone()),
            _ => Some(ChcExpr::Op(ChcOp::And, all)),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{ChcExpr, ChcOp, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause};
    use std::sync::Arc;

    /// Each branch is conjoined to the guard simplified once per split: the
    /// guard's `true` and duplicate conjuncts vanish, the branch follows the
    /// guard conjuncts, and a branch that contradicts a guard conjunct makes
    /// its clause trivially false (dropped).
    #[test]
    fn or_split_conjoins_each_branch_to_the_simplified_guard() {
        let mut problem = ChcProblem::new();
        let inv = problem.declare_predicate("inv", vec![ChcSort::Int]);
        let x = ChcVar::new("x", ChcSort::Int);
        let p = ChcExpr::var(ChcVar::new("p", ChcSort::Bool));
        let lower = ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0));
        let upper = ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(5));
        let constraint = ChcExpr::Op(
            ChcOp::And,
            vec![
                Arc::new(p.clone()),
                Arc::new(lower.clone()),
                Arc::new(ChcExpr::Bool(true)),
                Arc::new(lower.clone()),
                Arc::new(ChcExpr::or(ChcExpr::not(p.clone()), upper.clone())),
            ],
        );
        problem.add_clause(HornClause::new(
            ClauseBody::new(vec![(inv, vec![ChcExpr::var(x.clone())])], Some(constraint)),
            ClauseHead::Predicate(inv, vec![ChcExpr::var(x)]),
        ));

        problem.try_split_ors_in_clauses(8, false);

        let constraints: Vec<_> = problem
            .clauses()
            .iter()
            .map(|clause| clause.body.constraint.clone())
            .collect();
        assert_eq!(
            constraints,
            vec![Some(ChcExpr::Op(
                ChcOp::And,
                vec![
                    Arc::new(p),
                    Arc::new(lower.simplify_constants()),
                    Arc::new(upper.simplify_constants()),
                ],
            ))],
            "the (not p) branch contradicts the guard and is dropped"
        );
    }

    /// `conjoin` gives exactly `simplify_constants(and_all(guard ++ [branch]))`
    /// (with `true` as `None`): duplicates across guard and branch, nested
    /// conjunctions, and complementary pairs in either direction.
    #[test]
    fn conjoin_matches_simplify_constants_of_and_all() {
        use super::SimplifiedConjunction;
        let x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
        let p = ChcExpr::var(ChcVar::new("p", ChcSort::Bool));
        let q = ChcExpr::var(ChcVar::new("q", ChcSort::Bool));
        let lo = ChcExpr::ge(x.clone(), ChcExpr::int(0));
        let hi = ChcExpr::le(x, ChcExpr::int(3));
        let not_p = ChcExpr::not(p.clone());
        let cases: Vec<(Vec<ChcExpr>, ChcExpr)> = vec![
            (vec![], ChcExpr::Bool(true)),
            (vec![], lo.clone()),
            (vec![lo.clone()], ChcExpr::Bool(true)),
            (
                vec![lo.clone(), hi.clone()],
                ChcExpr::and(hi.clone(), q.clone()),
            ),
            (
                vec![ChcExpr::and(p.clone(), lo.clone())],
                ChcExpr::and(lo.clone(), q.clone()),
            ),
            (vec![p.clone(), lo.clone()], not_p.clone()),
            (
                vec![not_p.clone(), lo.clone()],
                ChcExpr::and(q.clone(), p.clone()),
            ),
            (vec![p.clone(), not_p.clone()], q.clone()),
            (vec![lo.clone(), ChcExpr::Bool(false)], q.clone()),
            (
                vec![lo.clone()],
                ChcExpr::and(q.clone(), ChcExpr::not(q.clone())),
            ),
        ];
        for (guard, branch) in cases {
            let expected = ChcExpr::and_all(guard.iter().cloned().chain([branch.clone()]))
                .simplify_constants();
            let expected = (expected != ChcExpr::Bool(true)).then_some(expected);
            assert_eq!(
                SimplifiedConjunction::from_conjuncts(guard.clone()).conjoin(branch.clone()),
                expected,
                "guard {guard:?} branch {branch:?}"
            );
        }
    }
}
