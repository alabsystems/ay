// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Complete typed sparse cost eligibility, never proof authority.
//! Array nodes are validated even when a later read drops a stored value.

use super::*;
use crate::checker::bv_bitblast::{
    MAX_PROOF_PRODUCING_CLAUSE_LITERALS as ROOTS, MAX_PROOF_PRODUCING_TERM_EDGES as EDGES,
    MAX_PROOF_PRODUCING_TERM_NODES as NODES,
};
use std::collections::HashMap;

mod bounds;
mod reads;
mod route;
mod shape;
#[cfg(test)]
mod tests;
use bounds::Bounds;
use shape::Operation;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct Cost {
    pub(super) work: usize,
    pub(super) name_work: usize,
    nodes: usize,
    edges: usize,
    roots: usize,
    occurrences: usize,
}

#[derive(Clone, Copy, Default)]
struct Node {
    references: usize,
    result: Option<Bounds>,
}
#[derive(Clone, Copy)]
enum Frame {
    Enter(TermId),
    Exit(TermId),
}

struct Census {
    nodes: HashMap<TermId, Node>,
    stack: Vec<Frame>,
    edges: usize,
    reads: usize,
    cursors: usize,
    requests: usize,
    transient: usize,
    saw_array: bool,
}

pub(super) fn plan(
    terms: &TermStore,
    clause: &[TermId],
    proof: &BvExprProofLimits,
    progress: Progress<'_>,
) -> Result<Option<Cost>, ProofCheckError> {
    // Primitive-key collections paid BEFORE allocating, not allocator/RSS.
    debit(
        progress,
        32 * (NODES + EDGES + ROOTS) + 256,
        2 * 1024 * 1024,
    )?;
    let result = match census(terms, clause, proof, progress) {
        Ok(Some(cost)) => route::price(terms, clause, proof, cost, progress),
        other => other,
    };
    if result.is_ok() {
        debit(progress, 1, 0)?;
    }
    result
}

fn census(
    terms: &TermStore,
    clause: &[TermId],
    proof: &BvExprProofLimits,
    progress: Progress<'_>,
) -> Result<Option<Cost>, ProofCheckError> {
    if clause.is_empty() || clause.len() > ROOTS {
        return Ok(None);
    }
    let mut census = Census {
        nodes: HashMap::new(),
        stack: Vec::new(),
        edges: 0,
        reads: 0,
        cursors: 0,
        requests: 0,
        transient: 0,
        saw_array: false,
    };
    if census.nodes.try_reserve(NODES).is_err()
        || census
            .stack
            .try_reserve_exact(EDGES + ROOTS + NODES)
            .is_err()
    {
        return Ok(None);
    }
    for &root in clause {
        debit(progress, 32, 0)?;
        if terms.entry_stamp(root).is_none() || terms.sort(root) != &Sort::Bool {
            return Ok(None);
        }
        census.stack.push(Frame::Enter(root));
    }
    while let Some(frame) = census.stack.pop() {
        debit(progress, 32, 0)?;
        let complete = match frame {
            Frame::Enter(term) => census.enter(terms, term),
            Frame::Exit(term) => census.exit(terms, term, progress)?,
        };
        if !complete {
            return Ok(None);
        }
    }
    Ok(bounds::finish(&census, clause, proof))
}

impl Census {
    fn enter(&mut self, terms: &TermStore, term: TermId) -> bool {
        if let Some(node) = self.nodes.get_mut(&term) {
            let Some(next) = node.references.checked_add(1) else {
                return false;
            };
            node.references = next;
            return node.result.is_some(); // active ancestor is a cycle
        }
        if self.nodes.len() == NODES {
            return false;
        }
        let Some((op, children)) = shape::inspect(terms, term) else {
            return false;
        };
        let Some(edges) = self.edges.checked_add(children.len()) else {
            return false;
        };
        if edges > EDGES || self.stack.len() + children.len() + 1 > EDGES + ROOTS + NODES {
            return false;
        }
        self.saw_array |= matches!(op, Operation::Array);
        self.edges = edges;
        self.nodes.insert(
            term,
            Node {
                references: 1,
                result: None,
            },
        );
        self.stack.push(Frame::Exit(term));
        self.stack
            .extend(children.iter().rev().copied().map(Frame::Enter));
        true
    }

    fn exit(
        &mut self,
        terms: &TermStore,
        term: TermId,
        progress: Progress<'_>,
    ) -> Result<bool, ProofCheckError> {
        let Some((op, children)) = shape::inspect(terms, term) else {
            return Ok(false);
        };
        let result = if matches!(op, Operation::Select) {
            let Some(read) = reads::inspect(terms, children, &self.nodes, progress)? else {
                return Ok(false);
            };
            let Some(j) = self.transient.checked_add(read.transient) else {
                return Ok(false);
            };
            let Some(p) = self.cursors.checked_add(read.cursors) else {
                return Ok(false);
            };
            let Some(a) = self.requests.checked_add(read.request_count) else {
                return Ok(false);
            };
            if self.nodes.len() + p > NODES || self.edges + a > EDGES {
                return Ok(false);
            }
            for requested in &read.requests[..read.request_count] {
                let Some(node) = self.nodes.get_mut(requested) else {
                    return Ok(false);
                };
                let Some(r) = node.references.checked_add(1) else {
                    return Ok(false);
                };
                node.references = r;
            }
            self.transient = j;
            self.cursors = p;
            self.requests = a;
            self.reads += 1;
            read.bound
        } else {
            let Some(bound) = bounds::node(op, children, &self.nodes) else {
                return Ok(false);
            };
            bound
        };
        let Some(node) = self.nodes.get_mut(&term) else {
            return Ok(false);
        };
        node.result = Some(result);
        Ok(true)
    }
}
