// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The query cone of a clause system, and the path encoding of a linear one.
//!
//! A derivation of `false` only ever uses clauses whose head lies in the
//! backward closure of the query bodies (the query cone), so everything else
//! is dropped here, dead-end cycles included, by a plain graph walk.
//!
//! In a LINEAR acyclic cone (every clause has at most one body predicate) a
//! derivation of `false` is a chain `fact -> P1 -> ... -> Pk -> query`. No
//! predicate repeats along it (that would be a cycle), so no clause repeats
//! either (each clause has one head). One copy of the arguments per predicate
//! and one fresh copy of the variables per clause therefore represent every
//! chain exactly:
//!
//! ```text
//!   OR { s_q : q a query clause }
//!   s_C => body_C(v_C) /\ r_Q /\ a_Q = args_C(v_C) /\ a_P = head_C(v_C)
//!   r_P => OR { s_C : C defines P }
//! ```
//!
//! with `s_C` "clause C is used", `r_P` "P is on the chain", `a_P` its
//! arguments and `v_C` C's own variables, renamed apart from every other
//! clause (the property `BmcSolver::mk_rule_vars` lost for head-only
//! variables). A real chain satisfies the formula by selecting exactly its
//! clauses; conversely a model selects a query and, following the `r`/`s`
//! implications back through the acyclic cone, a real chain. So `unsat`
//! means no derivation of `false` exists, and the formula has size linear in
//! the clause system where full inlining is exponential in the number of
//! branch points.

use super::NotConfirmed;
use crate::{ChcExpr, ChcProblem, ChcSort, ChcVar, ClauseHead, HornClause, PredicateId};
use std::collections::{BTreeMap, BTreeSet};

/// The clauses a derivation of `false` can use, in problem order.
pub(super) struct QueryCone<'a> {
    clauses: Vec<&'a HornClause>,
    predicates: BTreeSet<PredicateId>,
}

impl<'a> QueryCone<'a> {
    pub(super) fn of(problem: &'a ChcProblem) -> Self {
        let mut definitions: BTreeMap<PredicateId, Vec<&HornClause>> = BTreeMap::new();
        for clause in problem.clauses() {
            if let ClauseHead::Predicate(head, _) = &clause.head {
                definitions.entry(*head).or_default().push(clause);
            }
        }
        let mut predicates = BTreeSet::new();
        let mut pending: Vec<PredicateId> = problem
            .clauses()
            .iter()
            .filter(|clause| matches!(clause.head, ClauseHead::False))
            .flat_map(|clause| clause.body.predicates.iter().map(|(id, _)| *id))
            .collect();
        while let Some(predicate) = pending.pop() {
            if !predicates.insert(predicate) {
                continue;
            }
            for clause in definitions.get(&predicate).into_iter().flatten() {
                pending.extend(clause.body.predicates.iter().map(|(id, _)| *id));
            }
        }
        let clauses = problem
            .clauses()
            .iter()
            .filter(|clause| match &clause.head {
                ClauseHead::False => true,
                ClauseHead::Predicate(id, _) => predicates.contains(id),
            })
            .collect();
        Self {
            clauses,
            predicates,
        }
    }

    /// Kahn's algorithm over the cone's body -> head edges.
    pub(super) fn is_acyclic(&self) -> bool {
        let mut indegree: BTreeMap<PredicateId, usize> =
            self.predicates.iter().map(|id| (*id, 0)).collect();
        let mut successors: BTreeMap<PredicateId, Vec<PredicateId>> = BTreeMap::new();
        for clause in &self.clauses {
            if let ClauseHead::Predicate(head, _) = &clause.head {
                for (body, _) in &clause.body.predicates {
                    successors.entry(*body).or_default().push(*head);
                    *indegree.entry(*head).or_insert(0) += 1;
                }
            }
        }
        let mut ready: Vec<PredicateId> = indegree
            .iter()
            .filter(|(_, degree)| **degree == 0)
            .map(|(id, _)| *id)
            .collect();
        let mut removed = 0usize;
        while let Some(predicate) = ready.pop() {
            removed += 1;
            for head in successors.get(&predicate).into_iter().flatten() {
                if let Some(degree) = indegree.get_mut(head) {
                    *degree -= 1;
                    if *degree == 0 {
                        ready.push(*head);
                    }
                }
            }
        }
        removed == indegree.len()
    }

    pub(super) fn clauses(&self) -> impl Iterator<Item = &'a HornClause> + '_ {
        self.clauses.iter().copied()
    }

    pub(super) fn is_linear(&self) -> bool {
        self.clauses
            .iter()
            .all(|clause| clause.body.predicates.len() <= 1)
    }

    /// The path formula described in the module documentation.
    ///
    /// Constants are numbered by position WITHIN the cone (`p<k>` the k-th
    /// cone predicate, `c<k>`/`s<k>` the k-th cone clause), never by problem
    /// index, so the same cone renders the same script whether or not
    /// clauses outside it (a dead-end cycle) were stripped first. The
    /// confirmation memo relies on that.
    pub(super) fn path_formula(&self, problem: &ChcProblem) -> Result<ChcExpr, NotConfirmed> {
        let mut ordinal: BTreeMap<PredicateId, usize> = BTreeMap::new();
        let mut arguments: BTreeMap<PredicateId, Vec<ChcExpr>> = BTreeMap::new();
        for (position, predicate) in self.predicates.iter().enumerate() {
            let sorts = &problem
                .get_predicate(*predicate)
                .ok_or_else(|| NotConfirmed::Encoding("undeclared cone predicate".to_string()))?
                .arg_sorts;
            let copies = sorts
                .iter()
                .enumerate()
                .map(|(argument, sort)| fresh(format!("p{position}_a{argument}"), sort.clone()))
                .collect();
            ordinal.insert(*predicate, position);
            arguments.insert(*predicate, copies);
        }
        let reach = |predicate: &PredicateId| {
            let position = ordinal.get(predicate).copied().ok_or_else(|| {
                NotConfirmed::Encoding("predicate application outside the query cone".to_string())
            })?;
            Ok(fresh(format!("r{position}"), ChcSort::Bool))
        };
        let select = |position: usize| fresh(format!("s{position}"), ChcSort::Bool);

        let mut conjuncts = vec![ChcExpr::or_all(
            self.clauses
                .iter()
                .enumerate()
                .filter(|(_, clause)| matches!(clause.head, ClauseHead::False))
                .map(|(position, _)| select(position)),
        )];
        let mut definitions: BTreeMap<PredicateId, Vec<ChcExpr>> = self
            .predicates
            .iter()
            .map(|predicate| (*predicate, Vec::new()))
            .collect();
        for (position, clause) in self.clauses.iter().enumerate() {
            let renaming: Vec<(ChcVar, ChcExpr)> = clause
                .vars()
                .into_iter()
                .enumerate()
                .map(|(index, var)| {
                    let copy = fresh(format!("c{position}_v{index}"), var.sort.clone());
                    (var, copy)
                })
                .collect();
            let mut used = Vec::new();
            if let Some(constraint) = &clause.body.constraint {
                used.push(constraint.substitute(&renaming));
            }
            for (body, actuals) in &clause.body.predicates {
                used.push(reach(body)?);
                used.extend(equate(arguments.get(body), actuals, &renaming)?);
            }
            if let ClauseHead::Predicate(head, actuals) = &clause.head {
                used.extend(equate(arguments.get(head), actuals, &renaming)?);
                if let Some(defining) = definitions.get_mut(head) {
                    defining.push(select(position));
                }
            }
            conjuncts.push(ChcExpr::implies(select(position), ChcExpr::and_all(used)));
        }
        for (predicate, defining) in definitions {
            conjuncts.push(ChcExpr::implies(
                reach(&predicate)?,
                ChcExpr::or_all(defining),
            ));
        }
        Ok(ChcExpr::and_all(conjuncts))
    }
}

/// The name prefix of every constant in a path formula. (`__ay_*` is the
/// executor elaborator's reserved namespace and is refused on declaration.)
pub(super) const FRESH_PREFIX: &str = "__eac_";

/// A constant in a namespace no source variable reaches: every source
/// variable of a used clause is renamed to a `c<clause>_v<index>` copy, and
/// a problem whose own names use this prefix is refused before encoding.
fn fresh(suffix: String, sort: ChcSort) -> ChcExpr {
    ChcExpr::var(ChcVar::new(format!("{FRESH_PREFIX}{suffix}"), sort))
}

fn equate(
    copies: Option<&Vec<ChcExpr>>,
    actuals: &[ChcExpr],
    renaming: &[(ChcVar, ChcExpr)],
) -> Result<Vec<ChcExpr>, NotConfirmed> {
    let copies = copies.ok_or_else(|| {
        NotConfirmed::Encoding("predicate application outside the query cone".to_string())
    })?;
    if copies.len() != actuals.len() {
        return Err(NotConfirmed::Encoding(
            "predicate application arity mismatch".to_string(),
        ));
    }
    Ok(copies
        .iter()
        .zip(actuals)
        .map(|(copy, actual)| ChcExpr::eq(copy.clone(), actual.substitute(renaming)))
        .collect())
}
