// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Bounded breadth-first occurrence trees over the unmodified source clauses.
//!
//! Prefixes contain only source indices and ordered child slots. Every expansion
//! adds a new occurrence, even when another slot chose the same source clause.
//! Complete trees are emitted in body-order postorder; this keeps the prior
//! linear path ordering without sharing assignments across nonlinear siblings.

use std::collections::VecDeque;

use super::{Derivation, QuantifiedChcProblem, SourceControl, MAX_PATHS, MAX_PATH_CLAUSES};
use crate::{ClauseHead, HornClause, PredicateId};

const MAX_PREFIXES: usize = 256;

#[derive(Clone, Copy)]
struct Node {
    clause: usize,
    children: [Option<usize>; MAX_PATH_CLAUSES],
}

impl Node {
    const fn new(clause: usize) -> Self {
        Self {
            clause,
            children: [None; MAX_PATH_CLAUSES],
        }
    }
}

#[derive(Clone, Copy)]
struct Prefix {
    nodes: [Node; MAX_PATH_CLAUSES],
    len: usize,
}

enum Next {
    Complete,
    Open {
        node: usize,
        position: usize,
        predicate: PredicateId,
    },
}

pub(super) fn enumerate(
    problem: &QuantifiedChcProblem,
    control: &SourceControl<'_>,
) -> Option<Vec<Derivation>> {
    let clauses = problem.source_problem().clauses();
    let mut queue = VecDeque::new();
    let mut admitted = 0usize;
    for (index, clause) in clauses.iter().enumerate() {
        control.charge(1)?;
        if matches!(clause.head, ClauseHead::False)
            && clause.body.predicates.len() < MAX_PATH_CLAUSES
        {
            if admitted == MAX_PREFIXES {
                break;
            }
            reserve_prefix(&mut queue, control)?;
            let mut prefix = Prefix {
                nodes: [Node::new(0); MAX_PATH_CLAUSES],
                len: 1,
            };
            prefix.nodes[0] = Node::new(index);
            queue.push_back(prefix);
            admitted += 1;
        }
    }
    let mut trees = Vec::new();
    while let Some(prefix) = queue.pop_front() {
        control.charge(1)?;
        let Next::Open {
            node,
            position,
            predicate,
        } = next(&prefix, clauses, control)?
        else {
            control.bytes(std::mem::size_of::<Derivation>() * 2)?;
            trees.try_reserve(1).ok()?;
            trees.push(finish(&prefix, clauses, control)?);
            if trees.len() == MAX_PATHS {
                break;
            }
            continue;
        };
        if prefix.len == MAX_PATH_CLAUSES || admitted == MAX_PREFIXES {
            continue;
        }
        for (index, clause) in clauses.iter().enumerate() {
            control.charge(1)?;
            if matches!(&clause.head, ClauseHead::Predicate(head, _) if *head == predicate)
                && clause.body.predicates.len() < MAX_PATH_CLAUSES
            {
                reserve_prefix(&mut queue, control)?;
                let mut expanded = prefix;
                expanded.nodes[node].children[position] = Some(prefix.len);
                expanded.nodes[prefix.len] = Node::new(index);
                expanded.len += 1;
                queue.push_back(expanded);
                admitted += 1;
                if admitted == MAX_PREFIXES {
                    break;
                }
            }
        }
    }
    drop(queue);
    control.poll()?;
    Some(trees)
}

fn reserve_prefix(queue: &mut VecDeque<Prefix>, control: &SourceControl<'_>) -> Option<()> {
    // Charge the bounded arena copy before copying, plus geometric queue growth.
    // This is a deterministic copy ledger, not an allocator/RSS measurement.
    control.charge(MAX_PATH_CLAUSES)?;
    control.bytes(std::mem::size_of::<Prefix>() * 2)?;
    queue.try_reserve(1).ok()
}

fn next(prefix: &Prefix, clauses: &[HornClause], control: &SourceControl<'_>) -> Option<Next> {
    for (node, occurrence) in prefix.nodes[..prefix.len].iter().enumerate() {
        control.charge(1)?;
        let clause = clauses.get(occurrence.clause)?;
        for (position, (predicate, _)) in clause.body.predicates.iter().enumerate() {
            control.charge(1)?;
            if occurrence.children.get(position)?.is_none() {
                return Some(Next::Open {
                    node,
                    position,
                    predicate: *predicate,
                });
            }
        }
    }
    Some(Next::Complete)
}

fn finish(
    prefix: &Prefix,
    clauses: &[HornClause],
    control: &SourceControl<'_>,
) -> Option<Derivation> {
    control.bytes(
        prefix
            .len
            .checked_mul(std::mem::size_of::<usize>() + std::mem::size_of::<Vec<usize>>())?,
    )?;
    let mut result = Derivation {
        clause_indices: Vec::new(),
        premise_steps: Vec::new(),
    };
    result.clause_indices.try_reserve_exact(prefix.len).ok()?;
    result.premise_steps.try_reserve_exact(prefix.len).ok()?;
    let mut seen = [false; MAX_PATH_CLAUSES];
    let root = emit(0, prefix, clauses, &mut seen, &mut result, control)?;
    if root.checked_add(1)? != prefix.len || !seen[..prefix.len].iter().all(|seen| *seen) {
        return None;
    }
    control.poll()?;
    Some(result)
}

fn emit(
    node: usize,
    prefix: &Prefix,
    clauses: &[HornClause],
    seen: &mut [bool; MAX_PATH_CLAUSES],
    result: &mut Derivation,
    control: &SourceControl<'_>,
) -> Option<usize> {
    // Arena edges point strictly forward and there are at most eight nodes, so
    // this body-order postorder walk has a fixed, independently bounded stack.
    control.charge(1)?;
    if node >= prefix.len || seen[node] {
        return None;
    }
    seen[node] = true;
    let occurrence = &prefix.nodes[node];
    let clause = clauses.get(occurrence.clause)?;
    if matches!(clause.head, ClauseHead::False) != (node == 0) {
        return None;
    }
    let count = clause.body.predicates.len();
    control.bytes(count.checked_mul(std::mem::size_of::<usize>())?)?;
    let mut premises = Vec::new();
    premises.try_reserve_exact(count).ok()?;
    for (position, (wanted, args)) in clause.body.predicates.iter().enumerate() {
        control.charge(1)?;
        let child = (*occurrence.children.get(position)?)?;
        if child <= node || child >= prefix.len {
            return None;
        }
        let child_clause = clauses.get(prefix.nodes[child].clause)?;
        let ClauseHead::Predicate(head, head_args) = &child_clause.head else {
            return None;
        };
        if head != wanted || head_args.len() != args.len() {
            return None;
        }
        premises.push(emit(child, prefix, clauses, seen, result, control)?);
    }
    if occurrence
        .children
        .get(count..)?
        .iter()
        .any(Option::is_some)
    {
        return None;
    }
    let step = result.clause_indices.len();
    result.clause_indices.push(occurrence.clause);
    result.premise_steps.push(premises);
    Some(step)
}

#[cfg(test)]
mod tests;
