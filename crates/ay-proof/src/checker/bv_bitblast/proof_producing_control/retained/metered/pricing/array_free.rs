// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Conservative discount eligibility, NOT source facts or semantic validation.
//! Any array, unsupported node or incomplete bounded scan keeps legacy fees.

use super::*;
use crate::checker::bv_bitblast::{
    MAX_PROOF_PRODUCING_CLAUSE_LITERALS as ROOTS, MAX_PROOF_PRODUCING_TERM_EDGES as EDGES,
    MAX_PROOF_PRODUCING_TERM_NODES as NODES,
};
use std::collections::HashSet;

pub(super) fn certify(
    terms: &TermStore,
    clause: &[TermId],
    progress: Progress<'_>,
) -> Result<bool, ProofCheckError> {
    // Visits, fixed-width keys, collection copies and geometric bookkeeping:
    // this is logical work/storage, not a CPU-instruction/allocator-RSS claim.
    debit(progress, 8 * (NODES + EDGES + ROOTS) + 64, 2 * 1024 * 1024)?;
    if clause.is_empty() || clause.len() > ROOTS {
        return Ok(false);
    }
    let mut pending = Vec::new();
    pending
        .try_reserve_exact(EDGES + ROOTS)
        .map_err(|_| ProofCheckError::ResourceLimit)?;
    pending.extend_from_slice(clause);
    let mut seen = HashSet::new();
    seen.try_reserve(NODES)
        .map_err(|_| ProofCheckError::ResourceLimit)?;
    let result = walk(terms, &mut pending, &mut seen, progress);
    drop(seen);
    drop(pending);
    debit(progress, 1, 0)?;
    result
}

fn walk(
    terms: &TermStore,
    pending: &mut Vec<TermId>,
    seen: &mut HashSet<TermId>,
    progress: Progress<'_>,
) -> Result<bool, ProofCheckError> {
    let mut edges = 0usize;
    while let Some(term) = pending.pop() {
        debit(progress, 1, 0)?;
        if terms.entry_stamp(term).is_none() {
            return Ok(false);
        }
        if seen.contains(&term) {
            continue;
        }
        if seen.len() == NODES || !matches!(terms.sort(term), Sort::Bool | Sort::BitVec(_)) {
            return Ok(false);
        }
        seen.insert(term);
        let children_storage;
        let children = match terms.get(term) {
            TermData::Const(_) | TermData::Var(..) => &[][..],
            TermData::Not(child) => std::slice::from_ref(child),
            TermData::Ite(condition, yes, no) => {
                children_storage = [*condition, *yes, *no];
                &children_storage[..]
            }
            TermData::App(symbol, args) if args.len() <= 128 && admitted_symbol(symbol) => {
                args.as_slice()
            }
            _ => return Ok(false),
        };
        let Some(next_edges) = edges.checked_add(children.len()) else {
            return Ok(false);
        };
        if next_edges > EDGES {
            return Ok(false);
        }
        edges = next_edges;
        // All accepted extensions total <=EDGES; capacity was paid/reserved
        // before entry. No unchecked dynamic child collector is invoked.
        pending.extend_from_slice(children);
    }
    Ok(true)
}

// Long opaque symbol diagnostics and arbitrarily long indexed metadata have no
// source-dimensional cheap price here. They retain the exact legacy fees.
fn admitted_symbol(symbol: &Symbol) -> bool {
    if symbol.name().len() > 128 || matches!(symbol.name(), "select" | "store" | "const") {
        return false;
    }
    match symbol {
        Symbol::Named(_) => true,
        Symbol::Indexed(_, indices) => indices.len() <= 2,
        _ => false,
    }
}
