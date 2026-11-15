// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Private synthesis-only case split; original certificate queries stay whole.

use super::*;
use crate::{ChcOp, ClauseBody};

/// P AND (OR bad_i) -> false is equivalent to ALL P AND bad_i -> false.
/// Rewriting every branch separately lets the unchanged one-slot ghost
/// transform choose its observed index. No branch becomes original evidence.
pub(super) fn append_split_queries(
    out: &mut ChcProblem,
    problem: &QuantifiedChcProblem,
    transformer: &ArrayGhostPairTransformer,
    spec: &GhostPairSpec,
    clause: &HornClause,
    premises: &[crate::quantified::UniversalPremise],
    control: &SourceControl<'_>,
) -> Option<bool> {
    if spec.n != 1 || !matches!(clause.head, ClauseHead::False) {
        return Some(false);
    }
    let Some(constraint @ ChcExpr::Op(ChcOp::Or, _)) = clause.body.constraint.as_ref() else {
        return Some(false);
    };
    let leaves = super::super::super::candidate::anchors::positive_disjuncts_with_progress(
        constraint,
        &mut |amount| control.charge(amount),
    )?;
    for leaf in leaves {
        // Prepay the borrowed original body occurrence copies and the branch
        // root before copying Vec/Arc/name/sort payloads. Original clauses and
        // premises never mutate. Legacy native construction stays unchanged.
        source_premises::preflight_clause(clause, control)?;
        source_premises::preflight(leaf, control, &mut 0)?;
        control.charge(clause.body.predicates.len().checked_add(1)?)?;
        let header =
            std::mem::size_of::<HornClause>().checked_add(std::mem::size_of::<ClauseBody>())?;
        control.bytes(header.checked_mul(8)?)?;
        let mut branch = HornClause::query(ClauseBody::new(
            clause.body.predicates.clone(),
            Some(leaf.clone()),
        ));
        branch.action_id = clause.action_id;
        branch.source_query_ordinal = clause.source_query_ordinal;
        let names = crate::quantified::functions::controlled::names(problem, control)?;
        let rewritten =
            transformer.rewrite_source_clause(&branch, spec, premises, names, Some(control))?;
        // Conservative requested outer-vector growth/copy envelope, not an
        // allocator/RSS guarantee. Offer before add_clause can grow its Vec.
        control.charge(out.clauses().len().checked_add(1)?)?;
        control.bytes(
            out.clauses()
                .len()
                .checked_add(1)?
                .checked_mul(std::mem::size_of::<HornClause>())?
                .checked_mul(8)?,
        )?;
        out.add_clause(rewritten);
        drop(branch);
        control.poll()?;
    }
    control.poll()?;
    Some(true)
}

#[cfg(test)]
#[path = "query_anchors/tests.rs"]
mod tests;
