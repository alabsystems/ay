// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Work accounting for faithful, closed BV/array source reconstruction.

use ay_frontend::command::{Constant, ParsedSort, Term};

pub(super) const MAX_NODES: usize = 16_384;
pub(super) const MAX_DEPTH: usize = 96;
pub(super) const MAX_NODE_VISITS: usize = 1_048_576;
pub(super) const MAX_TOKEN_VISITS: usize = 8 * 1024 * 1024;

// Re-elaboration traverses each node once for every ancestor. Charge its
// actual depth, rather than multiplying every token by the deepest branch.
// The distinct generic provenance policy (which also renders and clones
// surfaces) is intentionally unchanged.
pub(super) fn work(root: &Term, context: Option<&ay_frontend::Context>) -> Option<(usize, usize)> {
    let mut pending = vec![(root, 0usize)];
    let (mut nodes, mut visits, mut bytes) = (0usize, 0usize, 0usize);
    while let Some((term, depth)) = pending.pop() {
        nodes = nodes.checked_add(1)?;
        if nodes > MAX_NODES || depth > MAX_DEPTH {
            return None;
        }
        let (local, children) = shape(term, context)?;
        visits = visits.checked_add(depth.checked_add(1)?)?;
        bytes = bytes.checked_add(local.checked_mul(depth.checked_add(1)?)?)?;
        if visits > MAX_NODE_VISITS
            || bytes > MAX_TOKEN_VISITS
            || nodes
                .checked_add(pending.len())?
                .checked_add(children.len())?
                > MAX_NODES
        {
            return None;
        }
        pending.extend(children.iter().map(|child| (child, depth + 1)));
    }
    Some((visits, bytes))
}

// The tree and shared-DAG builders accept exactly the same closed grammar.
pub(super) fn shape<'a>(
    term: &'a Term,
    context: Option<&ay_frontend::Context>,
) -> Option<(usize, &'a [Term])> {
    Some(match term {
        Term::Symbol(name) if name.len() <= 4096 => {
            if context.is_some_and(|ctx| ctx.is_defined_fun(name)) {
                return None;
            }
            (name.len(), &[])
        }
        Term::Const(Constant::True | Constant::False) => (5, &[]),
        Term::Const(Constant::Binary(text) | Constant::Hexadecimal(text)) if text.len() <= 130 => {
            (text.len(), &[])
        }
        Term::App(head, args) if head.len() <= 64 && args.len() <= 128 => {
            if context.is_some_and(|ctx| ctx.is_defined_fun(head)) {
                return None;
            }
            (head.len().checked_add(args.len())?.checked_add(2)?, args)
        }
        Term::IndexedApp(head, indices, args)
            if head.len() <= 64
                && indices.len() <= 2
                && args.len() <= 1
                && indices
                    .iter()
                    .all(|i| i.as_numeral().is_some_and(|n| n.len() <= 3)) =>
        {
            let index_bytes = indices.iter().try_fold(0usize, |sum, i| {
                sum.checked_add(i.as_numeral()?.len().checked_add(1)?)
            })?;
            (head.len().checked_add(index_bytes)?.checked_add(8)?, args)
        }
        Term::QualifiedApp(head, sort, args)
            if head.as_symbol() == Some("const") && args.len() == 1 && array_sort(sort) =>
        {
            (64, args)
        }
        _ => return None,
    })
}

fn array_sort(sort: &ParsedSort) -> bool {
    let ParsedSort::Parameterized(name, args) = sort else {
        return false;
    };
    name == "Array"
        && args.len() == 2
        && args.iter().all(|sort| {
            let ParsedSort::Indexed(name, indices) = sort else {
                return false;
            };
            name == "BitVec"
                && indices.len() == 1
                && indices[0].as_numeral().is_some_and(|n| {
                    n.len() <= 3
                        && n.parse::<u32>()
                            .is_ok_and(|width| (1..=128).contains(&width))
                })
        })
}

#[cfg(test)]
#[path = "proof_trust_surgery_surface_ground_tests.rs"]
mod tests;
