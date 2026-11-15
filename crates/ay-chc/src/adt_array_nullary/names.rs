// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! One source-disjoint naming plan shared by the formula and model pullback.

use super::{control::Control, MarkerDagNode};
use crate::{ChcExpr, ChcProblem, HornClause};
use ay_core::kani_compat::DetHashMap;

mod census;
use census::Census;

type Substitution = DetHashMap<String, ChcExpr>;

pub(super) struct Names {
    nodes: Vec<Substitution>,
    query: Substitution,
}

impl Names {
    pub(super) fn admit_source(problem: &ChcProblem, control: &Control) -> Option<()> {
        Census::new(control).problem(problem)
    }

    pub(super) fn capture(
        problem: &ChcProblem,
        nodes: &[MarkerDagNode],
        query: usize,
        control: &Control,
    ) -> Option<Self> {
        let mut census = Census::new(control);
        census.problem(problem)?;
        control.admit(nodes.len(), nodes.len().checked_mul(128)?)?;
        let mut maps = Vec::new();
        if maps.try_reserve_exact(nodes.len()).is_err() {
            return control.refuse();
        }
        for node in nodes {
            maps.push(census.substitution(problem.clauses().get(node.clause_idx)?)?);
        }
        let query = census.substitution(problem.clauses().get(query)?)?;
        control.poll()?;
        Some(Self { nodes: maps, query })
    }

    pub(super) fn node(&self, index: usize) -> Option<&Substitution> {
        self.nodes.get(index)
    }

    pub(super) fn query(&self) -> &Substitution {
        &self.query
    }
}

/// Every source clause component participates, including head-only locals and
/// query constraints. Borrowed roots avoid cloning before the owner's admission.
fn roots(clause: &HornClause) -> impl Iterator<Item = &ChcExpr> {
    let head: &[ChcExpr] = match &clause.head {
        crate::ClauseHead::Predicate(_, args) => args,
        crate::ClauseHead::False => &[],
    };
    clause
        .body
        .predicates
        .iter()
        .flat_map(|(_, args)| args)
        .chain(clause.body.constraint.iter())
        .chain(head)
}

#[cfg(test)]
mod tests;
