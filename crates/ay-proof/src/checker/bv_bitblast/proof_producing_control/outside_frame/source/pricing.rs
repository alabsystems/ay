// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Price original syntax attempts, never address truth or proof authority.

use super::*;

/// The caller prepays bounded n/edge/occurrence collections before entering.
/// The complete typed source excludes malformed IDs/types/cycles/huge names.
/// This returns an upper bound even when original address/write matching fails.
pub(in crate::checker::bv_bitblast::proof_producing_control) fn matching_work(
    terms: &TermStore,
    clause: &[TermId],
    useful_work: usize,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<Option<usize>, ProofCheckError> {
    let [negative] = clause else {
        return Ok(Some(0));
    };
    let TermData::Not(root) = terms.get(*negative) else {
        return Ok(Some(0));
    };
    let (Some(facts), Some(nodes)) = (
        boolean_nodes(terms, *root, true),
        boolean_nodes(terms, *root, false),
    ) else {
        return Ok(Some(0));
    };
    let Some(syntax_work) = syntax_work(terms, &facts, &nodes) else {
        return Ok(None);
    };
    // Refuse numeric eligibility BEFORE the potentially quadratic syntax walk.
    if syntax_work >= useful_work {
        return Ok(None);
    }
    if !progress(syntax_work, 0) {
        return Err(ProofCheckError::ResourceLimit);
    }
    let mut targets = 0usize;
    for guard in facts {
        let Some([end, length]) = syntax::ge(terms, guard) else {
            continue;
        };
        let Sort::BitVec(sort) = terms.sort(end) else {
            continue;
        };
        if sort.width == 0 || sort.width > 128 {
            continue;
        }
        let Some(length) = constant(terms, length, sort.width) else {
            continue;
        };
        if length == 0 || length > 64 {
            continue;
        }
        for &property in &nodes {
            if syntax::property(terms, property, end)
                .and_then(|(outside, _, _)| syntax::outside(terms, outside, end))
                .is_some()
            {
                let Some(next) = targets.checked_add(1) else {
                    return Ok(None);
                };
                targets = next;
            }
        }
    }
    // Each target may make2*65 start/end attempts and2*64*65 write/address
    // attempts, plus64 paired stripping and65 loop/refusal boundaries.
    //32Ki logical records*256 covers these and constant helper reads/drops.
    Ok(targets
        .checked_mul(32768)
        .and_then(|n| n.checked_mul(256))
        .and_then(|n| n.checked_add(syntax_work)))
}

fn syntax_work(terms: &TermStore, facts: &[TermId], nodes: &[TermId]) -> Option<usize> {
    let guards = facts
        .iter()
        .filter(|&&term| syntax::ge(terms, term).is_some())
        .count();
    let rows = nodes.iter().try_fold(0usize, |sum, &term| {
        let arity = match terms.get(term) {
            TermData::App(_, args) => args.len(),
            _ => 0,
        };
        sum.checked_add(
            1usize
                .checked_add(arity)?
                .checked_add(arity.checked_mul(arity)?)?,
        )
    })?;
    guards.checked_mul(rows)?.checked_mul(64)?.checked_mul(256)
}
