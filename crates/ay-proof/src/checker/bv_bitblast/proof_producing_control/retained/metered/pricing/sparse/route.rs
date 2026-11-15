// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Prepaid original matching envelope; the selector itself remains unchanged.

use super::*;
use bounds::{add, mul};

pub(super) fn price(
    terms: &TermStore,
    clause: &[TermId],
    proof: &BvExprProofLimits,
    mut cost: Cost,
    progress: Progress<'_>,
) -> Result<Option<Cost>, ProofCheckError> {
    let Some(useful) = mul(proof.max_leaf_name_bytes, 16)
        .and_then(|old| old.checked_sub(cost.work.checked_add(cost.name_work)?))
    else {
        return Ok(None);
    };
    // All collection/head/edge costs before numeric source matching. Three
    // disjoint forests use occurrence W, not distinct DAG n/e. Outside's two
    // walks charge raw pending/hash requests as well as distinct expansions.
    let Some(basic) = basic_work(cost) else {
        return Ok(None);
    };
    if basic >= useful {
        return Ok(None);
    }
    debit(progress, basic, 2 * 1024 * 1024)?;
    let candidates = crate::checker::bv_bitblast::disjoint::candidate_bound(terms, clause);
    let Some(disjoint) = mul(candidates, 4096)
        .and_then(|n| add(n, 1))
        .and_then(|n| mul(n, 256))
    else {
        return Ok(None);
    };
    let Some(before_outside) = add(basic, disjoint) else {
        return Ok(None);
    };
    if before_outside >= useful {
        return Ok(None);
    }
    let Some(outside) =
        outside_frame::matching_work(terms, clause, useful - before_outside, progress)?
    else {
        return Ok(None);
    };
    let Some(route) = add(before_outside, outside) else {
        return Ok(None);
    };
    if route >= useful {
        return Ok(None);
    }
    let Some(total) = add(cost.work, route) else {
        return Ok(None);
    };
    cost.work = total;
    Ok(Some(cost))
}

fn basic_work(cost: Cost) -> Option<usize> {
    let primitive = [cost.nodes, cost.edges, cost.roots]
        .into_iter()
        .try_fold(1, add)?;
    mul(
        add(add(mul(primitive, 64)?, mul(cost.occurrences, 16)?)?, 8192)?,
        256,
    )
}
