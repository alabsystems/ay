// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Complete per-read trace, not last-write-only or address truth authority.

use super::*;
use bounds::{add, checked, Bounds};
const STORES: usize = 64; // existing sparse lane ceiling, never raised
const REQUESTS: usize = 2 * STORES + 2;
const ADDRESS_DEPTH: usize = 16;

#[derive(Clone, Copy, Default)]
struct Store {
    index: Bounds,
    value: Bounds,
}
pub(super) struct Read {
    pub(super) bound: Bounds,
    pub(super) transient: usize,
    pub(super) cursors: usize,
    pub(super) requests: [TermId; REQUESTS],
    pub(super) request_count: usize,
}
impl Read {
    fn request(&mut self, term: TermId) -> bool {
        if self.request_count == REQUESTS {
            return false;
        }
        self.requests[self.request_count] = term;
        self.request_count += 1;
        true
    }
}

pub(super) fn inspect(
    terms: &TermStore,
    children: &[TermId],
    nodes: &HashMap<TermId, Node>,
    progress: Progress<'_>,
) -> Result<Option<Read>, ProofCheckError> {
    let [array, key] = children else {
        return Ok(None);
    };
    let Some(index) = nodes.get(key).and_then(|node| node.result) else {
        return Ok(None);
    };
    if index.address_depth > ADDRESS_DEPTH {
        return Ok(None);
    }
    let mut read = Read {
        bound: Bounds::default(),
        transient: 0,
        cursors: 0,
        requests: [TermId::SENTINEL; REQUESTS],
        request_count: 0,
    };
    if !read.request(*key) {
        return Ok(None);
    }
    let mut stores = [Store::default(); STORES];
    let mut count = 0;
    let mut cursor = *array;
    let base = loop {
        debit(progress, 32, 0)?;
        read.cursors += 1;
        if read.cursors > STORES + 1 {
            return Ok(None);
        }
        match terms.get(cursor) {
            TermData::Var(..) => {
                break Bounds {
                    nodes: 1,
                    depth: 1,
                    ..Bounds::default()
                }
            }
            TermData::App(Symbol::Named(op), args) => match (op.as_str(), args.as_slice()) {
                ("const-array", [fill]) => {
                    if !read.request(*fill) {
                        return Ok(None);
                    }
                    let Some(fill) = nodes.get(fill).and_then(|node| node.result) else {
                        return Ok(None);
                    };
                    break fill;
                }
                ("store", [previous, at, value]) if count < STORES => {
                    if !read.request(*at) || !read.request(*value) {
                        return Ok(None);
                    }
                    let (Some(at), Some(value)) = (
                        nodes.get(at).and_then(|node| node.result),
                        nodes.get(value).and_then(|node| node.result),
                    ) else {
                        return Ok(None);
                    };
                    if at.address_depth > ADDRESS_DEPTH {
                        return Ok(None);
                    }
                    stores[count] = Store { index: at, value };
                    count += 1;
                    cursor = *previous;
                }
                _ => return Ok(None),
            },
            _ => return Ok(None),
        }
    };
    let Sort::Array(array_sort) = terms.sort(*array) else {
        return Ok(None);
    };
    let mask = usize::from(matches!(&array_sort.element_sort, Sort::BitVec(w) if w.width > 1));
    let Some(source) = children
        .iter()
        .try_fold(0usize, |height, child| {
            Some(height.max(nodes.get(child)?.result?.source_depth))
        })
        .and_then(|height| add(height, 1))
    else {
        return Ok(None);
    };
    let Some((bound, transient)) = recurrence(index, base, &stores[..count], mask, source) else {
        return Ok(None);
    };
    read.bound = bound;
    read.transient = transient;
    Ok(Some(read))
}

fn recurrence(
    index: Bounds,
    base: Bounds,
    stores: &[Store],
    mask: usize,
    source: usize,
) -> Option<(Bounds, usize)> {
    let mut value = base;
    let mut transient = add(index.nodes, base.nodes)?;
    for store in stores.iter().rev() {
        let condition = add(add(index.nodes, store.index.nodes)?, 1)?;
        let output = add(
            add(value.nodes, store.value.nodes)?,
            add(2usize.checked_mul(add(condition, mask)?)?, 4)?,
        )?;
        let height = add(add(index.depth.max(store.index.depth), 1)?, add(mask, 3)?)?
            .max(add(store.value.depth, 2)?)
            .max(add(value.depth, 2)?);
        let footprint = [
            index.nodes,
            store.index.nodes,
            store.value.nodes,
            value.nodes,
            output,
        ]
        .into_iter()
        .try_fold(16usize, add)?;
        transient = add(transient, footprint)?;
        value = checked(Bounds {
            nodes: output,
            depth: height,
            source_depth: source,
            address_depth: 0,
        })?;
    }
    checked(Bounds {
        source_depth: source,
        address_depth: 0,
        ..value
    })
    .map(|bound| (bound, transient))
}
