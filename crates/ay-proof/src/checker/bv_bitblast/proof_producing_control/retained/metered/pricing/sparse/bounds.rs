// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Checked occurrence/multiplicity/transient costs; no proof authority.

use super::*;
use crate::checker::bv_bitblast::{
    MAX_PROOF_PRODUCING_CONSTRUCTED_EXPR_NODES as CONSTRUCTED,
    MAX_PROOF_PRODUCING_EXPR_DEPTH as DEPTH,
};

#[derive(Clone, Copy, Default)]
pub(super) struct Bounds {
    pub(super) nodes: usize,
    pub(super) depth: usize,
    pub(super) source_depth: usize,
    pub(super) address_depth: usize,
}
pub(super) fn add(a: usize, b: usize) -> Option<usize> {
    a.checked_add(b)
}
pub(super) fn mul(a: usize, b: usize) -> Option<usize> {
    a.checked_mul(b)
}
fn weighted(items: &[(usize, usize)], base: usize) -> Option<usize> {
    items
        .iter()
        .try_fold(base, |sum, &(n, weight)| add(sum, mul(n, weight)?))
}
pub(super) fn levels(arity: usize) -> usize {
    if arity <= 1 {
        0
    } else {
        usize::BITS as usize - (arity - 1).leading_zeros() as usize
    }
}
pub(super) fn checked(bound: Bounds) -> Option<Bounds> {
    (bound.nodes <= CONSTRUCTED && bound.depth <= DEPTH && bound.source_depth <= DEPTH)
        .then_some(bound)
}

pub(super) fn node(
    operation: Operation,
    children: &[TermId],
    nodes: &HashMap<TermId, Node>,
) -> Option<Bounds> {
    let (mut occurrences, mut height, mut source, mut address) = (0, 0, 0, 0);
    for child in children {
        let result = nodes.get(child)?.result?;
        occurrences = add(occurrences, result.nodes)?;
        height = height.max(result.depth);
        source = source.max(result.source_depth);
        address = address.max(result.address_depth);
    }
    let (extra, join) = match operation {
        Operation::Atom => (1, 1),
        Operation::Unary => (1, 1),
        Operation::Binary { extra, .. } => (extra, extra),
        Operation::Balanced if children.is_empty() => (1, 1),
        // Singleton AND/OR erases its source operator in actual lowering.
        // Retain one upper node here so N also bounds source walk pushes.
        Operation::Balanced => ((children.len() - 1).max(1), levels(children.len())),
        Operation::Array => {
            return checked(Bounds {
                source_depth: add(source, 1)?,
                ..Bounds::default()
            })
        }
        Operation::Select => return None,
    };
    checked(Bounds {
        nodes: add(occurrences, extra)?,
        depth: add(height, join)?,
        source_depth: add(source, 1)?,
        address_depth: if matches!(operation, Operation::Binary { address: true, .. }) {
            add(address, 1)?
        } else {
            0
        },
    })
}

pub(super) fn finish(
    census: &Census,
    clause: &[TermId],
    proof: &BvExprProofLimits,
) -> Option<Cost> {
    if !census.saw_array || census.reads == 0 {
        return None;
    }
    let (mut l, mut m, mut h, mut roots) = (0, 0, 0, 0);
    for node in census.nodes.values() {
        let result = node.result?;
        l = add(l, result.nodes)?;
        m = add(m, mul(node.references, result.nodes)?)?;
        h = h.max(result.depth);
    }
    for root in clause {
        roots = add(roots, census.nodes.get(root)?.result?.nodes)?;
    }
    let (n, e, q, s, p, a, j) = (
        census.nodes.len(),
        census.edges,
        clause.len(),
        census.reads,
        census.cursors,
        census.requests,
        census.transient,
    );
    let w = add(roots, q)?;
    let c = weighted(&[(l, 3), (m, 2), (j, 8), (q, 2)], 2)?;
    // Raw source edges PLUS every complete read request conservatively
    // overcount actual requests. Store cursor/edge walks are separate.
    if add(n, p)? > NODES
        || add(add(e, a)?, q)? > EDGES
        || add(e, mul(p, 3)?)? > EDGES
        || c > CONSTRUCTED
        || w > proof.max_expr_occurrences
        || add(h, levels(q))? > proof.max_expr_depth.min(DEPTH)
    {
        return None;
    }
    // N(scalar) >= its unrolled scalar source occurrences. Contains-read
    // stops at SELECT before array children; AND facts' OR leaves have
    // disjoint occurrence subtrees. All three disjoint walks <=3W, including
    // raw pushes, even with DAG/root sharing. Do not use distinct-source e.
    let tree = add(add(l, m)?, add(j, w)?)?;
    let primitive = [n, e, q, a, p, s].into_iter().try_fold(1, add)?;
    let b = add(add(mul(tree, 16)?, mul(primitive, 64)?)?, 8192)?;
    let names = weighted(&[(l, 4), (m, 2), (j, 4), (n, 1), (s, 1)], 1)?;
    let name_bytes = add(mul(names, 42)?, mul(n, 32)?)?;
    let work = add(mul(b, 256)?, mul(name_bytes, 16)?)?;
    let name_work = mul(proof.max_leaf_name_bytes.min(mul(w, 42)?), 16)?;
    (add(work, name_work)? < mul(proof.max_leaf_name_bytes, 16)?).then_some(Cost {
        work,
        name_work,
        nodes: n,
        edges: e,
        roots: q,
        occurrences: w,
    })
}
