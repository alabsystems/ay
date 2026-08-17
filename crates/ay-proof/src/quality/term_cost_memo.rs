// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Cancellation-aware memoization of proof term unfolding cost.

use ay_core::kani_compat::{DetHashMap, DetHashSet};
use ay_core::{TermData, TermId, TermStore};

use super::{charge_progress, checked_add_usize, ProofCheckError};

/// Maximum memo operations between caller-owned cancellation/deadline polls.
pub(super) const TERM_COST_MEMO_POLL_INTERVAL: usize = 1_024;

/// Validation-scoped memo for the pure tree-unfolding cost
/// `cost(t) = 1 + sum(cost(child))`.
///
/// Only pure costs are shared across steps. The parent module still performs
/// the full per-step payload walk because those charges bound decode/clone
/// work that recurs for every citing proof step.
#[derive(Debug, Default)]
pub(super) struct TermCostMemo {
    costs: DetHashMap<TermId, usize>,
}

fn poll(
    operations: &mut usize,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(), ProofCheckError> {
    *operations = checked_add_usize(*operations, 1)?;
    if operations.is_multiple_of(TERM_COST_MEMO_POLL_INTERVAL) {
        charge_progress(progress, 0, 0)?;
    }
    Ok(())
}

fn push_child(
    children: &mut Vec<TermId>,
    child: TermId,
    operations: &mut usize,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(), ProofCheckError> {
    poll(operations, progress)?;
    children.push(child);
    Ok(())
}

fn append_children_polled(
    terms: &TermStore,
    term: TermId,
    children: &mut Vec<TermId>,
    operations: &mut usize,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(), ProofCheckError> {
    match terms.get(term) {
        TermData::App(_, args) => {
            for &child in args {
                push_child(children, child, operations, progress)?;
            }
        }
        TermData::Let(bindings, body) => {
            for (_, child) in bindings {
                push_child(children, *child, operations, progress)?;
            }
            push_child(children, *body, operations, progress)?;
        }
        TermData::Not(child) => push_child(children, *child, operations, progress)?,
        TermData::Ite(condition, then_branch, else_branch) => {
            push_child(children, *condition, operations, progress)?;
            push_child(children, *then_branch, operations, progress)?;
            push_child(children, *else_branch, operations, progress)?;
        }
        TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
            push_child(children, *body, operations, progress)?;
            for trigger in triggers {
                for &child in trigger {
                    push_child(children, child, operations, progress)?;
                }
            }
        }
        _ => {}
    }
    Ok(())
}

/// Exact checked tree-unfolding cost over `roots`, memoized across steps.
///
/// Positive work/byte debits were already paid by the parent's per-step walk.
/// Zero-debit polls preserve caller-owned cancellation, deadline, and memory
/// controls throughout cold fills, high-fanout scheduling, warm root scans,
/// and the final sum.
pub(super) fn unfolded_work_memoized(
    memo: &mut TermCostMemo,
    terms: &TermStore,
    roots: &[TermId],
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<usize, ProofCheckError> {
    let mut active: DetHashSet<TermId> = DetHashSet::default();
    let mut stack: Vec<(TermId, bool)> = Vec::new();
    let mut children: Vec<TermId> = Vec::new();
    let mut operations = 0_usize;

    for &root in roots {
        poll(&mut operations, progress)?;
        if memo.costs.contains_key(&root) {
            continue;
        }
        stack.push((root, false));
        while let Some((term, expanded)) = stack.pop() {
            poll(&mut operations, progress)?;
            if memo.costs.contains_key(&term) {
                continue;
            }
            if expanded {
                active.remove(&term);
                children.clear();
                append_children_polled(terms, term, &mut children, &mut operations, progress)?;
                let mut cost = 1_usize;
                for &child in &children {
                    poll(&mut operations, progress)?;
                    let child_cost = memo
                        .costs
                        .get(&child)
                        .copied()
                        .ok_or(ProofCheckError::ResourceLimit)?;
                    cost = checked_add_usize(cost, child_cost)?;
                }
                memo.costs.insert(term, cost);
                continue;
            }

            if !active.insert(term) {
                return Err(ProofCheckError::ResourceLimit);
            }
            stack.push((term, true));
            children.clear();
            append_children_polled(terms, term, &mut children, &mut operations, progress)?;
            for &child in children.iter().rev() {
                poll(&mut operations, progress)?;
                if active.contains(&child) {
                    return Err(ProofCheckError::ResourceLimit);
                }
                if !memo.costs.contains_key(&child) {
                    stack.push((child, false));
                }
            }
        }
    }

    let mut total = 0_usize;
    for root in roots {
        poll(&mut operations, progress)?;
        total = checked_add_usize(
            total,
            memo.costs
                .get(root)
                .copied()
                .ok_or(ProofCheckError::ResourceLimit)?,
        )?;
    }
    Ok(total)
}
