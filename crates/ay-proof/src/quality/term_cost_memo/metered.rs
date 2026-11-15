// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Positive resource charges for the memo's own graph traversal and storage.

use std::collections::BTreeSet;
use std::mem::size_of;

use super::*;

#[cfg(test)]
mod tests;

type Progress<'a> = &'a mut dyn FnMut(usize, usize) -> bool;

#[derive(Clone, Copy)]
enum Frame {
    Enter(TermId),
    Finish(TermId),
}

/// Compute the same exact `1 + sum(child costs)` measure as the legacy helper,
/// including repeated edges and roots, under positive caller-owned charges.
///
/// The memo MUST remain scoped to one immutable TermStore snapshot, as in the
/// existing strict validation walk; this helper does not mint store identity.
/// Cancellation may retain only fully computed pure costs in the memo. They
/// grant no proof authority and remain valid for retry on that same snapshot.
/// No partially computed node cost is inserted. Missing handles, cycles,
/// unsupported future variants, and accounting overflow fail closed with the
/// existing typed `ResourceLimit` boundary, never by indexing a bad handle.
pub(in crate::quality) fn unfolded_work_memoized_with_progress(
    memo: &mut TermCostMemo,
    terms: &TermStore,
    roots: &[TermId],
    progress: Progress<'_>,
) -> Result<usize, ProofCheckError> {
    charge_progress(progress, 0, 0)?;
    let mut active = BTreeSet::new();
    let mut stack = Vec::new();
    let mut children = Vec::new();
    for &root in roots {
        charge_progress(progress, 1, 0)?;
        checked_term(terms, root, progress)?;
        if memo_get(memo, root, progress)?.is_some() {
            continue;
        }
        push(&mut stack, Frame::Enter(root), progress)?;
        loop {
            charge_progress(progress, 1, 0)?;
            let Some(frame) = stack.pop() else {
                break;
            };
            let (Frame::Enter(term) | Frame::Finish(term)) = frame;
            let data = checked_term(terms, term, progress)?;
            if memo_get(memo, term, progress)?.is_some() {
                continue;
            }
            match frame {
                Frame::Finish(_) => {
                    charge_progress(progress, tree_slots(active.len())?, 0)?;
                    if !active.remove(&term) {
                        return Err(ProofCheckError::ResourceLimit);
                    }
                    append_children(data, &mut children, progress)?;
                    let mut cost = 1usize;
                    for &child in &children {
                        charge_progress(progress, 1, 0)?;
                        checked_term(terms, child, progress)?;
                        let child_cost = memo_get(memo, child, progress)?
                            .ok_or(ProofCheckError::ResourceLimit)?;
                        cost = checked_add_usize(cost, child_cost)?;
                    }
                    memo_insert(memo, term, cost, progress)?;
                }
                Frame::Enter(_) => {
                    tree_lookup(active.len(), progress)?;
                    let slots = tree_slots(active.len())?;
                    charge_progress(
                        progress,
                        slots,
                        mul(
                            slots,
                            checked_add_usize(size_of::<TermId>(), size_of::<usize>())?,
                        )?,
                    )?;
                    if !active.insert(term) {
                        return Err(ProofCheckError::ResourceLimit);
                    }
                    push(&mut stack, Frame::Finish(term), progress)?;
                    append_children(data, &mut children, progress)?;
                    for &child in children.iter().rev() {
                        charge_progress(progress, 1, 0)?;
                        checked_term(terms, child, progress)?;
                        tree_lookup(active.len(), progress)?;
                        if active.contains(&child) {
                            return Err(ProofCheckError::ResourceLimit);
                        }
                        if memo_get(memo, child, progress)?.is_none() {
                            push(&mut stack, Frame::Enter(child), progress)?;
                        }
                    }
                }
            }
        }
    }
    let mut total = 0usize;
    for &root in roots {
        charge_progress(progress, 1, 0)?;
        checked_term(terms, root, progress)?;
        let cost = memo_get(memo, root, progress)?.ok_or(ProofCheckError::ResourceLimit)?;
        total = checked_add_usize(total, cost)?;
    }
    charge_progress(progress, 0, 0)?;
    Ok(total)
}

fn checked_term<'a>(
    terms: &'a TermStore,
    term: TermId,
    progress: Progress<'_>,
) -> Result<&'a TermData, ProofCheckError> {
    charge_progress(progress, 1, 0)?;
    if term.index() >= terms.len() {
        return Err(ProofCheckError::ResourceLimit);
    }
    Ok(terms.get(term))
}

fn append_children(
    data: &TermData,
    children: &mut Vec<TermId>,
    progress: Progress<'_>,
) -> Result<(), ProofCheckError> {
    charge_progress(progress, 1, 0)?;
    children.clear();
    match data {
        TermData::App(_, args) => {
            for &child in args {
                push(children, child, progress)?;
            }
        }
        TermData::Let(bindings, body) => {
            for (_, child) in bindings {
                push(children, *child, progress)?;
            }
            push(children, *body, progress)?;
        }
        TermData::Not(child) => push(children, *child, progress)?,
        TermData::Ite(condition, then_branch, else_branch) => {
            push(children, *condition, progress)?;
            push(children, *then_branch, progress)?;
            push(children, *else_branch, progress)?;
        }
        TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
            push(children, *body, progress)?;
            for trigger in triggers {
                // Empty groups still cost iteration; do not hide their scan
                // inside a flattening iterator with a single outer poll.
                charge_progress(progress, 1, 0)?;
                for &child in trigger {
                    push(children, child, progress)?;
                }
            }
        }
        TermData::Const(_) | TermData::Var(..) => {}
        _ => return Err(ProofCheckError::ResourceLimit),
    }
    Ok(())
}

fn push<T>(values: &mut Vec<T>, value: T, progress: Progress<'_>) -> Result<(), ProofCheckError> {
    charge_progress(progress, 1, 0)?;
    if values.len() == values.capacity() {
        let capacity = mul(values.capacity().max(2), 2)?;
        let bytes = mul(capacity, size_of::<T>())?;
        charge_progress(progress, checked_add_usize(bytes, 1)?, bytes)?;
        let additional = capacity
            .checked_sub(values.len())
            .ok_or(ProofCheckError::ResourceLimit)?;
        values
            .try_reserve_exact(additional)
            .map_err(|_| ProofCheckError::ResourceLimit)?;
    }
    values.push(value);
    Ok(())
}

fn tree_lookup(entries: usize, progress: Progress<'_>) -> Result<(), ProofCheckError> {
    let levels = checked_add_usize((usize::BITS - entries.leading_zeros()) as usize, 1)?;
    charge_progress(
        progress,
        checked_add_usize(entries, 1)?.min(mul(levels, 12)?),
        0,
    )
}

fn tree_slots(entries: usize) -> Result<usize, ProofCheckError> {
    // alloc's B=6 tree has 11 keys and 12 edges. Splits/merges touch at most
    // one node per level plus a root, even as the active path shrinks/grows.
    mul(
        checked_add_usize((usize::BITS - entries.leading_zeros()) as usize, 2)?,
        32,
    )
}

fn memo_get(
    memo: &TermCostMemo,
    term: TermId,
    progress: Progress<'_>,
) -> Result<Option<usize>, ProofCheckError> {
    memo_lookup(memo, progress)?;
    Ok(memo.costs.get(&term).copied())
}

fn memo_lookup(memo: &TermCostMemo, progress: Progress<'_>) -> Result<(), ProofCheckError> {
    tree_lookup(memo.costs.len(), progress)
}

fn memo_insert(
    memo: &mut TermCostMemo,
    term: TermId,
    cost: usize,
    progress: Progress<'_>,
) -> Result<(), ProofCheckError> {
    memo_lookup(memo, progress)?;
    let slots = tree_slots(memo.costs.len())?;
    charge_progress(
        progress,
        slots,
        mul(
            slots,
            checked_add_usize(size_of::<(TermId, usize)>(), size_of::<usize>())?,
        )?,
    )?;
    charge_progress(progress, 0, 0)?;
    memo.costs.insert(term, cost);
    Ok(())
}

fn mul(left: usize, right: usize) -> Result<usize, ProofCheckError> {
    left.checked_mul(right)
        .ok_or(ProofCheckError::ResourceLimit)
}
