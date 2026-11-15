// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Breadth-first, original-index linear paths; no rewritten reachability input.

use std::collections::VecDeque;

use super::{QuantifiedChcProblem, SourceControl, MAX_PATHS, MAX_PATH_CLAUSES};
use crate::ClauseHead;

const MAX_PREFIXES: usize = 256;

pub(super) fn enumerate(
    problem: &QuantifiedChcProblem,
    control: &SourceControl<'_>,
) -> Option<Vec<Vec<usize>>> {
    let clauses = problem.source_problem().clauses();
    let mut queue = VecDeque::new();
    let mut admitted = 0usize;
    for (index, clause) in clauses.iter().enumerate() {
        control.charge(1)?;
        if matches!(clause.head, ClauseHead::False) && clause.body.predicates.len() <= 1 {
            if admitted == MAX_PREFIXES {
                break;
            }
            control.bytes(std::mem::size_of::<usize>() * MAX_PATH_CLAUSES * 2)?;
            queue.try_reserve(1).ok()?;
            queue.push_back(vec![index]);
            admitted += 1;
        }
    }
    let mut paths = Vec::new();
    while let Some(reverse_path) = queue.pop_front() {
        control.charge(1)?;
        let current = clauses.get(*reverse_path.last()?)?;
        if current.body.predicates.is_empty() {
            let mut path = reverse_path;
            path.reverse();
            paths.try_reserve(1).ok()?;
            paths.push(path);
            if paths.len() == MAX_PATHS {
                break;
            }
            continue;
        }
        if reverse_path.len() == MAX_PATH_CLAUSES || admitted == MAX_PREFIXES {
            continue;
        }
        let [(wanted, _)] = current.body.predicates.as_slice() else {
            continue;
        };
        for (index, clause) in clauses.iter().enumerate() {
            control.charge(1)?;
            if matches!(&clause.head, ClauseHead::Predicate(head, _) if head == wanted)
                && clause.body.predicates.len() <= 1
            {
                control.bytes(std::mem::size_of::<usize>() * MAX_PATH_CLAUSES * 2)?;
                queue.try_reserve(1).ok()?;
                let mut next = Vec::new();
                next.try_reserve_exact(reverse_path.len().checked_add(1)?)
                    .ok()?;
                next.extend_from_slice(&reverse_path);
                next.push(index);
                queue.push_back(next);
                admitted += 1;
                if admitted == MAX_PREFIXES {
                    break;
                }
            }
        }
    }
    drop(queue);
    control.poll()?;
    Some(paths)
}

#[cfg(test)]
mod tests;
