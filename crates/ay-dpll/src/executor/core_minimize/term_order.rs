// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Deterministic term-complexity ordering for core deletion candidates.

use ay_core::kani_compat::DetHashMap;
use ay_core::{TermData, TermId, TermStore};

/// Stable-sort candidates by memoized term node count.
///
/// Tree size is computed over the hash-consed DAG: each distinct subterm's
/// size is computed once, while shared subterms count at every occurrence.
/// Saturating arithmetic makes deeply shared DAGs deterministic without
/// overflow. The iterative post-order avoids recursion on deeply nested axiom
/// bodies.
pub(super) fn sort_by_node_count(terms: &TermStore, candidates: &mut [TermId]) {
    let mut memo: DetHashMap<TermId, u64> = DetHashMap::default();
    candidates.sort_by_key(|term| term_node_count(terms, &mut memo, *term));
}

fn term_node_count(terms: &TermStore, memo: &mut DetHashMap<TermId, u64>, root: TermId) -> u64 {
    fn children(data: &TermData, out: &mut Vec<TermId>) {
        match data {
            TermData::Const(_) | TermData::Var(..) => {}
            TermData::App(_, args) => out.extend_from_slice(args),
            TermData::Let(bindings, body) => {
                out.extend(bindings.iter().map(|(_, term)| *term));
                out.push(*body);
            }
            TermData::Not(term) => out.push(*term),
            TermData::Ite(condition, then_term, else_term) => {
                out.extend([*condition, *then_term, *else_term]);
            }
            TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
                out.push(*body);
                out.extend(triggers.iter().flatten().copied());
            }
            // `TermData` is non-exhaustive; future leaf-or-unknown variants
            // count as size one and preserve deterministic ordering.
            _ => {}
        }
    }

    let mut stack = vec![(root, false)];
    let mut children_buf = Vec::new();
    while let Some((term, expanded)) = stack.pop() {
        if memo.contains_key(&term) {
            continue;
        }
        children_buf.clear();
        children(terms.get(term), &mut children_buf);
        if expanded {
            let mut count = 1_u64;
            for child in &children_buf {
                count = count.saturating_add(memo.get(child).copied().unwrap_or(1));
            }
            memo.insert(term, count);
        } else {
            stack.push((term, true));
            for child in &children_buf {
                if !memo.contains_key(child) {
                    stack.push((*child, false));
                }
            }
        }
    }
    memo.get(&root).copied().unwrap_or(1)
}
